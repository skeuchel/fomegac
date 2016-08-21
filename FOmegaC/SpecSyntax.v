Require Import Coq.Lists.List.
Require Export ParDB.Spec.
Require Export ParDB.Lemmas.
Require Export ParDB.Inst.

Implicit Types x y α β c : Ix.

Inductive Kind : Type :=
  | kstar
  | karr (k1 k2 : Kind).

Implicit Types k : Kind.

Inductive Exp : Type :=
  | var        x
  (**********************)
  | τabs       k (τ: Exp)
  | τapp       (τ1 τ2: Exp)
  | arr        (τ1 τ2: Exp)
  | arrτ       k (τ: Exp)
  | arrγ       (τ1 τ2: Exp) k (τ3: Exp)
  (**********************)
  | coτabs     k (γ: Exp)
  | coτapp     (γ1 γ2: Exp)
  | coarr      (γ1 γ2: Exp)
  | coarrτ     k (γ: Exp)
  | coarrγ     (γ1 γ2: Exp) k (γ: Exp)
  | coinvarr₁  (γ: Exp)
  | coinvarr₂  (γ: Exp)
  | coinvarrτ  (γ1 γ2: Exp)
  | coinvarrγ₁ (γ: Exp)
  | coinvarrγ₂ (γ: Exp)
  | coinvarrγ₃ (γ: Exp)
  | cobeta     k (γ1 γ2: Exp)
  | corefl     (τ: Exp)
  | cosym      (γ: Exp)
  | cotrans    (γ1 γ2: Exp)
  (**********************)
  | abs        (τ s: Exp)
  | absτ       k (s: Exp)
  | absγ       (τ1 τ2: Exp) k (s : Exp)
  | app        (s1 s2 : Exp)
  | appτ       (s τ: Exp)
  | appγ       (s γ: Exp)
  | cast       (s γ: Exp).

Implicit Types e s τ γ : Exp.

(* Inductive Env : Set := *)
(*   | nil *)
(*   | tmvar (Γ: Env) τ *)
(*   | tyvar (Γ: Env) k *)
(*   | covar (Γ: Env) τ1 τ2 k. *)

Inductive Binding : Type :=
  | tyvar k
  | covar τ1 τ2 k
  | tmvar τ.

Definition Env : Type := list Binding.
Implicit Types Γ : Env.

(* Notation "Γ ▻ τ"           := (tmvar Γ τ) (at level 55, left associativity). *)
(* Notation "Γ ► k"           := (tyvar Γ k) (at level 55, left associativity). *)
(* Notation "Γ ◅ τ1 ~ τ2 ∷ k" := (covar Γ τ1 τ2 k) (at level 55, left associativity). *)
Notation "Γ ▻ τ"           := (cons (tmvar τ) Γ) (at level 55, left associativity).
Notation "Γ ► k"           := (cons (tyvar k) Γ) (at level 55, left associativity).
Notation "Γ ◅ τ1 ~ τ2 ∷ k" := (cons (covar τ1 τ2 k) Γ) (at level 55, left associativity).

Section DeBruijn.

  Context {X: Type}.
  Context {vrX: Vr X}.
  Context {wkX: Wk X}.
  Context {vrExp: Vr Exp}.
  Context {liftXExp: Lift X Exp}.

  Fixpoint apExp (ζ: Sub X) (e: Exp) {struct e} : Exp :=
    match e with
      | var x            =>  lift (ζ x)
      (**************************************************************)
      | τabs k τ         =>  τabs k τ[ζ↑]
      | τapp τ1 τ2       =>  τapp τ1[ζ] τ2[ζ]
      | arr  τ1 τ2       =>  arr  τ1[ζ] τ2[ζ]
      | arrτ k τ         =>  arrτ k τ[ζ↑]
      | arrγ τ1 τ2 k τ3  =>  arrγ τ1[ζ] τ2[ζ] k τ3[ζ]
      (**************************************************************)
      | coτabs k γ       =>  coτabs k γ[ζ↑]
      | coτapp γ1 γ2     =>  coτapp γ1[ζ] γ2[ζ]
      | coarr γ1 γ2      =>  coarr γ1[ζ] γ2[ζ]
      | coarrτ k γ       =>  coarrτ k γ[ζ↑]
      | coarrγ γ1 γ2 k γ =>  coarrγ γ1[ζ] γ2[ζ] k γ[ζ]
      | coinvarr₁ γ      =>  coinvarr₁ γ[ζ]
      | coinvarr₂ γ      =>  coinvarr₂ γ[ζ]
      | coinvarrτ γ1 γ2  =>  coinvarrτ γ1[ζ] γ2[ζ]
      | coinvarrγ₁ γ     =>  coinvarrγ₁ γ[ζ]
      | coinvarrγ₂ γ     =>  coinvarrγ₂ γ[ζ]
      | coinvarrγ₃ γ     =>  coinvarrγ₃ γ[ζ]
      | cobeta k γ1 γ2   =>  cobeta k γ1[ζ↑] γ2[ζ]
      | corefl τ         =>  corefl τ[ζ]
      | cosym γ          =>  cosym γ[ζ]
      | cotrans γ1 γ2    =>  cotrans γ1[ζ] γ2[ζ]
      (**************************************************************)
      | abs  τ s         =>  abs  τ[ζ] s[ζ↑]
      | absτ k s         =>  absτ k s[ζ↑]
      | absγ τ1 τ2 k s   =>  absγ τ1[ζ] τ2[ζ] k s[ζ↑]
      | app  s1 s2       =>  app  s1[ζ] s2[ζ]
      | appτ s τ         =>  appτ s[ζ] τ[ζ]
      | appγ s γ         =>  appγ s[ζ] γ[ζ]
      | cast s γ         =>  cast s[ζ] γ[ζ]
    end
  where "t '[' ζ ']'" := (apExp ζ t).

  Definition apBinding (ζ: Sub X) (b: Binding) : Binding :=
    match b with
      | tmvar τ       => tmvar τ[ζ]
      | tyvar k       => tyvar k
      | covar τ1 τ2 k => covar τ1[ζ] τ2[ζ] k
    end.

End DeBruijn.

Instance vrExp : Vr Exp := {| vr := var |}.
Proof. inversion 1; auto. Defined.

Ltac crushSyntaxMatch :=
  match goal with
    | [H: cons _ _       = cons _ _       |- _] => inversion H; clear H; subst*
    | [H: var _          = var _          |- _] => inversion H; clear H; subst*
    | [H: τabs _ _       = τabs _ _       |- _] => inversion H; clear H; subst*
    | [H: τapp _ _       = τapp _ _       |- _] => inversion H; clear H; subst*
    | [H: arr _ _        = arr _ _        |- _] => inversion H; clear H; subst*
    | [H: arrτ _ _       = arrτ _ _       |- _] => inversion H; clear H; subst*
    | [H: arrγ _ _ _ _   = arrγ _ _ _ _   |- _] => inversion H; clear H; subst*
    | [H: coτabs _ _     = coτabs _ _     |- _] => inversion H; clear H; subst*
    | [H: coτapp _ _     = coτapp _ _     |- _] => inversion H; clear H; subst*
    | [H: coarr _ _      = coarr _ _      |- _] => inversion H; clear H; subst*
    | [H: coarrτ _ _     = coarrτ _ _     |- _] => inversion H; clear H; subst*
    | [H: coarrγ _ _ _ _ = coarrγ _ _ _ _ |- _] => inversion H; clear H; subst*
    | [H: coinvarr₁ _    = coinvarr₁ _    |- _] => inversion H; clear H; subst*
    | [H: coinvarr₂ _    = coinvarr₂ _    |- _] => inversion H; clear H; subst*
    | [H: coinvarrτ _ _  = coinvarrτ _ _  |- _] => inversion H; clear H; subst*
    | [H: coinvarrγ₁ _   = coinvarrγ₁ _   |- _] => inversion H; clear H; subst*
    | [H: coinvarrγ₂ _   = coinvarrγ₂ _   |- _] => inversion H; clear H; subst*
    | [H: coinvarrγ₃ _   = coinvarrγ₃ _   |- _] => inversion H; clear H; subst*
    | [H: cobeta _ _     = cobeta _ _     |- _] => inversion H; clear H; subst*
    | [H: corefl _       = corefl _       |- _] => inversion H; clear H; subst*
    | [H: cosym _        = cosym _        |- _] => inversion H; clear H; subst*
    | [H: cotrans _ _    = cotrans _ _    |- _] => inversion H; clear H; subst*
    | [H: abs _ _        = abs _ _        |- _] => inversion H; clear H; subst*
    | [H: absτ _ _       = absτ _ _       |- _] => inversion H; clear H; subst*
    | [H: absγ _ _ _ _   = absγ _ _ _ _   |- _] => inversion H; clear H; subst*
    | [H: app _ _        = app _ _        |- _] => inversion H; clear H; subst*
    | [H: appτ _ _       = appτ _ _       |- _] => inversion H; clear H; subst*
    | [H: appγ _ _       = appγ _ _       |- _] => inversion H; clear H; subst*
    | [H: cast _ _       = cast _ _       |- _] => inversion H; clear H; subst*

    | [ |- cons _ _       = cons _ _       ] => f_equal
    | [ |- var _          = var _          ] => f_equal
    | [ |- τabs _ _       = τabs _ _       ] => f_equal
    | [ |- τapp _ _       = τapp _ _       ] => f_equal
    | [ |- arr _ _        = arr _ _        ] => f_equal
    | [ |- arrτ _ _       = arrτ _ _       ] => f_equal
    | [ |- arrγ _ _ _ _   = arrγ _ _ _ _   ] => f_equal
    | [ |- coτabs _ _     = coτabs _ _     ] => f_equal
    | [ |- coτapp _ _     = coτapp _ _     ] => f_equal
    | [ |- coarr _ _      = coarr _ _      ] => f_equal
    | [ |- coarrτ _ _     = coarrτ _ _     ] => f_equal
    | [ |- coarrγ _ _ _ _ = coarrγ _ _ _ _ ] => f_equal
    | [ |- coinvarr₁ _    = coinvarr₁ _    ] => f_equal
    | [ |- coinvarr₂ _    = coinvarr₂ _    ] => f_equal
    | [ |- coinvarrτ _ _  = coinvarrτ _ _  ] => f_equal
    | [ |- coinvarrγ₁ _   = coinvarrγ₁ _   ] => f_equal
    | [ |- coinvarrγ₂ _   = coinvarrγ₂ _   ] => f_equal
    | [ |- coinvarrγ₃ _   = coinvarrγ₃ _   ] => f_equal
    | [ |- cobeta _ _     = cobeta _ _     ] => f_equal
    | [ |- corefl _       = corefl _       ] => f_equal
    | [ |- cosym _        = cosym _        ] => f_equal
    | [ |- cotrans _ _    = cotrans _ _    ] => f_equal
    | [ |- abs _ _        = abs _ _        ] => f_equal
    | [ |- absτ _ _       = absτ _ _       ] => f_equal
    | [ |- absγ _ _ _ _   = absγ _ _ _ _   ] => f_equal
    | [ |- app _ _        = app _ _        ] => f_equal
    | [ |- appτ _ _       = appτ _ _       ] => f_equal
    | [ |- appγ _ _       = appγ _ _       ] => f_equal
    | [ |- cast _ _       = cast _ _       ] => f_equal
  end.

Ltac crushSyntaxRefold :=
  match goal with
    | [ H: context[apExp ?ζ ?e] |- _ ] =>
      change (apExp ζ e) with e[ζ] in H
    | [ H: context[List.map (ap ?ζ) ?es] |- _ ] =>
      change (List.map (ap ζ) es) with es[ζ] in H
    | [ |- context[apExp ?ζ ?e] ] =>
      change (apExp ζ e) with e[ζ]
    | [ |- context[List.map (ap ?ζ) ?es] ] =>
      change (List.map (ap ζ) es) with es[ζ]
    (* | [ H: context[apBinding ?ζ ?b] |- _ ] => *)
    (*   change (apBinding ζ b) with b[ζ] in H *)
    (* | [ |- context[apBinding ?ζ ?b] ] => *)
    (*   change (apBinding ζ b) with b[ζ] *)
  end.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     rewrite ?ap_comp, ?comp_up, ?up_liftSub, ?up_comp_lift;
     repeat crushSyntaxRefold;
     repeat crushSyntaxMatch;
     eauto;
     idtac).

Local Ltac derive :=
  crush; f_equal; crush.

Module ExpKit <: Kit.

  Definition TM := Exp.
  Definition inst_vr := vrExp.

  Section Application.

    Context {Y: Type}.
    Context {vrY : Vr Y}.
    Context {wkY: Wk Y}.
    Context {liftY: Lift Y Exp}.

    Global Instance inst_ap : Ap Exp Y := {| ap := apExp |}.
    Proof. induction x; derive. Defined.

    Global Instance inst_ap_vr : LemApVr Exp Y := {}.
    Proof. reflexivity. Qed.

  End Application.

  Instance inst_ap_inj: LemApInj Exp Ix := {}.
  Proof.
    intros m Inj_m x. revert m Inj_m.
    induction x; destruct y; simpl; try discriminate;
    inversion 1; subst; f_equal; eauto using InjSubIxUp.
  Qed.

  Instance inst_ap_comp (Y Z: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y Exp}
    {vrZ: Vr Z} {wkZ: Wk Z} {liftZ: Lift Z Exp}
    {apYZ: Ap Y Z} {compUpYZ: LemCompUp Y Z}
    {apLiftYExpZ: LemApLift Y Z Exp} :
    LemApComp Exp Y Z := {}.
  Proof. induction x; derive. Qed.

  Instance inst_ap_liftSub (Y: Type)
    {vrY: Vr Y} {wkY: Wk Y} {liftY: Lift Y Exp} :
    LemApLiftSub Exp Y := {}.
  Proof. induction t; derive. Qed.

  Lemma inst_ap_ixComp (t: Exp) :
    ∀ (ξ: Sub Ix) (ζ: Sub Exp), t[ξ][ζ] = t[⌈ξ⌉ >=> ζ].
  Proof. induction t; derive. Qed.

End ExpKit.

Section ApplicationListExp.

  Context {X: Type}.
  Context {vrX : Vr X}.
  Context {wkX: Wk X}.
  Context {liftXUExp: Lift X Exp}.

  Global Instance ApListExp : Ap (list Exp) X :=
    {| ap := fun ζ => map (ap ζ) |}.
  Proof. induction x; crush. Defined.

End ApplicationListExp.

Section ApplicationBinding.

  Context {X: Type}.
  Context {vrX : Vr X}.
  Context {wkX: Wk X}.
  Context {liftXUExp: Lift X Exp}.

  Global Instance ApBinding : Ap Binding X := {| ap := apBinding |}.
  Proof. induction x; crush. Defined.

End ApplicationBinding.

Section LemmasBinding.

  Context {X Y: Type}.
  Context {vrX : Vr X} {wkX: Wk X} {liftXUExp: Lift X Exp}.
  Context {vrY : Vr Y} {wkY: Wk Y} {liftYUExp: Lift Y Exp}.
  Context {apXY : Ap X Y}.
  Context {apCompExpXY: LemApComp Exp X Y}.

  Global Instance LemApCompBinding : LemApComp Binding X Y := {}.
  Proof. destruct x; crush. Qed.

End LemmasBinding.

Module InstExp := Inst ExpKit.
Export InstExp. (* Export for shorter names. *)
