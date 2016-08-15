
Require Export ParDB.Spec.
Require Export ParDB.Lemmas.
Require Export ParDB.Inst.

Implicit Types x y α β c : Ix.

Inductive Kind : Type :=
  | kstar
  | karr (k1 k2 : Kind).

Implicit Types k : Kind.

Inductive Tm : Type :=
  | var      x
  (**********************)
  | absee    (τ e: Tm)
  | absτe    k (e: Tm)
  | absγe    (τ1 τ2: Tm) k (e : Tm)
  | appee    (e1 e2 : Tm)
  | appeτ    (e τ: Tm)
  | appeγ    (e γ: Tm)
  | cast     (e γ: Tm)
  (**********************)
  | absττ    k (τ: Tm)
  | appττ    (τ1 τ2: Tm)
  | arree    (τ1 τ2: Tm)
  | arrτe    k (τ: Tm)
  | arrγe    (τ1 τ2: Tm) k (τ3: Tm)
  (**********************)
  | γabsττ   k (γ: Tm)
  | γappττ   (γ1 γ2: Tm)
  | γarree   (γ1 γ2: Tm)
  | γarrτe   k (γ: Tm)
  | γarrγe   (τ1 τ2 γ: Tm)
  | γbeta    (γ1 γ2: Tm)
  | γsym     (γ: Tm)
  | γtrans   (γ1 γ2: Tm).

Implicit Types t e τ γ : Tm.

Inductive Env : Set :=
  | nil
  | evar (Γ: Env) τ
  | τvar (Γ: Env) k
  | γvar (Γ: Env) τ1 τ2 k.

Implicit Types Γ : Env.

Notation "Γ ▻ τ"           := (evar Γ τ) (at level 55, left associativity).
Notation "Γ ► k"           := (τvar Γ k) (at level 55, left associativity).
Notation "Γ ◅ τ1 ~ τ2 ∷ k" := (γvar Γ τ1 τ2 k) (at level 55, left associativity).

Section DeBruijn.

  Context {X: Type}.
  Context {vrX: Vr X}.
  Context {wkX: Wk X}.
  Context {vrTm: Vr Tm}.
  Context {liftXTm: Lift X Tm}.

  Fixpoint apTm (ζ: Sub X) (t: Tm) {struct t} : Tm :=
    match t with
      | var x            =>  lift (ζ x)
      (**************************************************************)
      | absee τ e        =>  absee τ[ζ] e[ζ↑]
      | absτe k e        =>  absτe k e[ζ↑]
      | absγe τ1 τ2 k e  =>  absγe τ1[ζ] τ2[ζ] k e[ζ↑]
      | appee e1 e2      =>  appee e1[ζ] e2[ζ]
      | appeτ e τ        =>  appeτ e[ζ] τ[ζ]
      | appeγ e γ        =>  appeγ e[ζ] γ[ζ]
      | cast e γ         =>  cast e[ζ] γ[ζ]
      (**************************************************************)
      | absττ k τ        =>  absττ k τ[ζ↑]
      | appττ τ1 τ2      =>  appττ τ1[ζ] τ2[ζ]
      | arree τ1 τ2      =>  arree τ1[ζ] τ2[ζ]
      | arrτe k τ        =>  arrτe k τ[ζ↑]
      | arrγe τ1 τ2 k τ3 =>  arrγe τ1[ζ] τ2[ζ] k τ3[ζ↑]
      (**************************************************************)
      | γabsττ k γ       =>  γabsττ k γ[ζ↑]
      | γappττ γ1 γ2     =>  γappττ γ1[ζ] γ2[ζ]
      | γarree γ1 γ2     =>  γarree γ1[ζ] γ2[ζ]
      | γarrτe k γ       =>  γarrτe k γ[ζ↑]
      | γarrγe τ1 τ2 γ   =>  γarrγe τ1[ζ] τ2[ζ] γ[ζ↑]
      | γbeta γ1 γ2      =>  γbeta γ1[ζ] γ2[ζ]
      | γsym γ           =>  γsym γ[ζ]
      | γtrans γ1 γ2     =>  γtrans γ1[ζ] γ2[ζ]
    end
  where "t '[' ζ ']'" := (apTm ζ t).

End DeBruijn.

Instance vrTm : Vr Tm := {| vr := var |}.
Proof. inversion 1; auto. Defined.

Module TmKit <: Kit.

  Definition TM := Tm.
  Definition inst_vr := vrTm.

  Local Ltac refold :=
    match goal with
      | [ |- context[apTm ?ξ ?t] ] =>
        change (apTm ξ t) with t[ξ]
    end.

  Local Ltac crush :=
    intros; cbn in * |-;
    repeat
      (cbn;
       repeat crushDbSyntaxMatchH;
       repeat crushDbLemmasMatchH;
       rewrite ?comp_up, ?up_liftSub, ?up_comp_lift;
       repeat refold);
    auto.

  Local Ltac derive :=
    crush; f_equal; crush.

  Section Application.

    Context {Y: Type}.
    Context {vrY : Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y Tm}.

    Global Instance inst_ap : Ap Tm Y := {| ap := apTm |}.
    Proof. induction x; derive. Defined.

    Global Instance inst_ap_vr : LemApVr Tm Y := {}.
    Proof. reflexivity. Qed.

  End Application.

  Instance inst_ap_inj: LemApInj Tm Ix := {}.
  Proof.
    intros m Inj_m x. revert m Inj_m.
    induction x; destruct y; simpl; try discriminate;
    inversion 1; subst; f_equal; eauto using InjSubIxUp.
  Qed.

  Instance inst_ap_comp (Y Z: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y Tm}
    {vrZ: Vr Z} {wkZ: Wk Z} {liftZ: Lift Z Tm}
    {apYZ: Ap Y Z} {compUpYZ: LemCompUp Y Z}
    {apLiftYTmZ: LemApLift Y Z Tm} :
    LemApComp Tm Y Z := {}.
  Proof. induction x; derive. Qed.

  Instance inst_ap_liftSub (Y: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y Tm} :
    LemApLiftSub Tm Y := {}.
  Proof. induction t; derive. Qed.

  Lemma inst_ap_ixComp (t: Tm) :
    ∀ (ξ: Sub Ix) (ζ: Sub Tm), t[ξ][ζ] = t[⌈ξ⌉ >=> ζ].
  Proof. induction t; derive. Qed.

End TmKit.

Module InstTm := Inst TmKit.
Export InstTm. (* Export for shorter names. *)
