Require Import Coq.Lists.List.
Require Export ParDB.Spec.
Require Export ParDB.Lemmas.
Require Export ParDB.Inst.

Require Export SpecSyntax.
Require Export SpecTyping.
Require Export LemmasTyping.
Require Export Agreement.

Definition CoVarClosed (Γ: Env) : Prop :=
  ∀ c σ τ k, ¬ ⟨ c : σ ~ τ ∷ k ∈ Γ ⟩.

Lemma covarclosed_nil :
  CoVarClosed nil.
Proof. inversion 1. Qed.
Hint Resolve covarclosed_nil : ws.

Lemma covarclosed_up_tyvar {Γ k} :
  CoVarClosed Γ → CoVarClosed (Γ ► k).
Proof.
  unfold CoVarClosed, not; intros clΓ;
    inversion 1; subst; eauto.
Qed.
Hint Resolve covarclosed_up_tyvar : ws.

Local Ltac crushCoVarLookup :=
  match goal with
    | [H: ⟨ _ : _ ~ _ ∷ _ ∈ ?Γ ⟩ |- _] =>
      let clΓ := fresh "clΓ" in
        assert (clΓ: CoVarClosed Γ) by eauto with ws;
        elimtype False; apply (clΓ _ _ _ _ H)
  end.

Ltac crushIH :=
  repeat
    match goal with
      | [IH: WfEnv ?Γ → _ |- _ ] =>
        let wΓ := fresh "wΓ" in
        assert (wΓ: WfEnv Γ) by eauto with ws;
          specialize (IH wΓ); clear wΓ
      | [IH: CoVarClosed ?Γ → _ |- _ ] =>
        let clΓ := fresh "clΓ" in
        assert (clΓ: CoVarClosed Γ) by eauto with ws;
          specialize (IH clΓ); clear clΓ
    end.

(* Record Consistent (Γ : Env) : Prop := *)
(*   { arr_cons : ∀ {c τ1 τ2 σ}, *)
(*                  ⟨ c : arr τ1 τ2 ~ σ ∷ kstar ∈ Γ ⟩ → *)
(*                  ∃ σ1 σ2, σ = arr σ1 σ2 *)
(*   }. *)

Local Ltac crush :=
  intros;
  crushIH;
  repeat
    (cbn in *;
     repeat crushSyntaxMatch;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasRewriteH;
     repeat crushSyntaxRefold;
     repeat crushTypingMatchH;
     subst*;
     try discriminate;
     try crushCoVarLookup;
     eauto with ws;
     destruct_conjs;
     idtac
    );
  eauto 200 with ws.


Lemma arr_consistency {Γ γs σ1 σ2 τ} (clΓ: CoVarClosed Γ)
  (wγs: ⟨ Γ ⊢ γs : arr σ1 σ2 ↝* τ ∷ kstar ⟩) :
  ∃ ν1 ν2, τ = arr ν1 ν2 ∧
    (∃ γs1, ⟨ Γ ⊢ γs1 : σ1 ↝* ν1 ∷ kstar ⟩) ∧
    (∃ γs2, ⟨ Γ ⊢ γs2 : σ2 ↝* ν2 ∷ kstar ⟩).
Proof. depind wγs; crush. Qed.

Lemma arrτ_consistency {Γ γs k σ τ} (clΓ: CoVarClosed Γ)
  (wγs: ⟨ Γ ⊢ γs : arrτ k σ ↝* τ ∷ kstar ⟩) :
  ∃ ν, τ = arrτ k ν ∧
    (∃ γs, ⟨ Γ ► k ⊢ γs : σ ↝* ν ∷ kstar ⟩).
Proof. depind wγs; crush. Qed.

Lemma arrγ_consistency {Γ γs σ1 σ2 σ3 τ k} (clΓ: CoVarClosed Γ)
  (wγs: ⟨ Γ ⊢ γs : arrγ σ1 σ2 k σ3 ↝* τ ∷ kstar ⟩) :
  ∃ ν1 ν2 ν3, τ = arrγ ν1 ν2 k ν3 ∧
    (∃ γs1, ⟨ Γ ⊢ γs1 : σ1 ↝* ν1 ∷ k ⟩) ∧
    (∃ γs2, ⟨ Γ ⊢ γs2 : σ2 ↝* ν2 ∷ k ⟩) ∧
    (∃ γs3, ⟨ Γ ⊢ γs3 : σ3 ↝* ν3 ∷ kstar ⟩).
Proof. depind wγs; crush. Qed.

(*************************************************************************)

Definition upRedSub (ζγ: Sub Exp) : Sub Exp :=
  ((ζγ >=> wkm Exp) · corefl (var 0)).

Fixpoint apRedSub (ζγ: Sub Exp) (τ: Exp) {struct τ} : Exp :=
  match τ with
    | var α              =>  ζγ α
    | τabs k τ           =>  coτabs k (apRedSub (upRedSub ζγ) τ)
    | τapp τ1 τ2         =>  coτapp (apRedSub ζγ τ1) (apRedSub ζγ τ2)
    | arr  τ1 τ2         =>  coarr  (apRedSub ζγ τ1) (apRedSub ζγ τ2)
    | arrτ k τ           =>  coarrτ k (apRedSub (upRedSub ζγ) τ)
    | arrγ τ1 τ2 k τ3    =>  coarrγ (apRedSub ζγ τ1) (apRedSub ζγ τ2) k (apRedSub ζγ τ3)
    | coτabs k γ         =>  coτabs k (apRedSub (upRedSub ζγ) γ)
    | coτapp γ1 γ2       =>  coτapp (apRedSub ζγ γ1) (apRedSub ζγ γ2)
    | coarr  γ1 γ2       =>  coarr  (apRedSub ζγ γ1) (apRedSub ζγ γ2)
    | coarrτ k γ         =>  coarrτ k (apRedSub (upRedSub ζγ) γ)
    | coarrγ γ1 γ2 k γ3  =>  coarrγ (apRedSub ζγ γ1) (apRedSub ζγ γ2) k (apRedSub ζγ γ3)
    | coinvarr₁ γ        =>  coinvarr₁ (apRedSub ζγ γ)
    | coinvarr₂ γ        =>  coinvarr₂ (apRedSub ζγ γ)
    | coinvarrτ γ1 γ2    =>  coinvarrτ (apRedSub ζγ γ1) (apRedSub ζγ γ2)
    | coinvarrγ₁ γ       =>  coinvarrγ₁ (apRedSub ζγ γ)
    | coinvarrγ₂ γ       =>  coinvarrγ₂ (apRedSub ζγ γ)
    | coinvarrγ₃ γ       =>  coinvarrγ₃ (apRedSub ζγ γ)
    | cobeta k γ1 γ2     =>  cobeta k (apRedSub (upRedSub ζγ) γ1) (apRedSub ζγ γ2)
    | corefl τ           =>  apRedSub ζγ τ
    | _ => var 0
  end.

Record WtRedSub (Γ Δ: Env) (ζγ ζ1 ζ2: Sub Exp) : Prop :=
  { wrs_tyvar : ∀ {α k},
                  ⟨ α ∷ k ∈ Γ ⟩ →
                  ⟨ Δ ⊢ ζγ α : ζ1 α ↝ ζ2 α ∷ k ⟩;
    wrs_covar : ∀ {c τ1 τ2 k},
                  ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ →
                  ⟨ Δ ⊢ ζγ c : τ1[ζ1] ↝ τ2[ζ2] ∷ k ⟩;
    wrs_left :> ⟨ ζ1 : Γ => Δ ⟩;
    wrs_right :> ⟨ ζ2 : Γ => Δ ⟩;
  }.

Hint Resolve wrs_tyvar : ws.
Hint Resolve wrs_covar : ws.
Hint Resolve wrs_left : ws.
Hint Resolve wrs_right : ws.

Lemma wtRedSub_up_tyvar {Γ Δ ζγ ζ1 ζ2} (wζ: WtRedSub Γ Δ ζγ ζ1 ζ2) :
  ∀ k, WtRedSub (Γ ► k) (Δ ► k) (upRedSub ζγ) ζ1↑ ζ2↑.
Proof.
  rewrite ?up_def.
  constructor; intros.
  - inversion H; clear H; crush.
    rewrite <- ?(ap_wkm_ix (X:=Exp)).
    crush.
  - inversion H; clear H; crush.
    rewrite ?ap_comp.
    rewrite ?wkm_snoc_cancel.
    rewrite <- ?ap_comp.
    rewrite <- ?(ap_wkm_ix (X:=Exp)).
    crush.
  - rewrite <- ?up_def; crush.
  - rewrite <- ?up_def; crush.
Qed.
Hint Resolve wtRedSub_up_tyvar : ws.

Lemma wtredsub_snoc_tyvar {Γ Δ ζγ ζ1 ζ2 γ σ τ k} :
  ⟨ Δ ⊢ γ : σ ↝ τ ∷ k ⟩ → ⟨ Δ ⊢ σ ∷ k ⟩ → ⟨ Δ ⊢ τ ∷ k ⟩ →
  WtRedSub Γ Δ ζγ ζ1 ζ2 →
  WtRedSub (Γ ► k) Δ (ζγ · γ) (ζ1 · σ) (ζ2 · τ).
Proof.
  intros; constructor; crush.
  rewrite ?ap_comp.
  rewrite ?wkm_snoc_cancel.
  crush.
Qed.

Lemma ty_redsub {Γ τ k} (wτ: ⟨ Γ ⊢ τ ∷ k ⟩) :
  ∀ Δ ζγ ζ1 ζ2,
    WtRedSub Γ Δ ζγ ζ1 ζ2 →
    ⟨ Δ ⊢ apRedSub ζγ τ : τ[ζ1] ↝ τ[ζ2] ∷ k ⟩.
Proof. induction wτ; crush. Qed.
Hint Resolve ty_redsub : ws.

Lemma red_redsub {Γ γ τ1 τ2 k} (wγ: ⟨ Γ ⊢ γ : τ1 ↝ τ2 ∷ k ⟩) :
  ∀ Δ ζγ ζ1 ζ2,
    WtRedSub Γ Δ ζγ ζ1 ζ2 →
    ⟨ Δ ⊢ apRedSub ζγ γ : τ1[ζ1] ↝ τ2[ζ2] ∷ k ⟩.
Proof. induction wγ; crush. Qed.
Hint Resolve red_redsub : ws.


(* Record WtRSSub (Γ Δ: Env) (ζγs: Sub (list Exp)) (ζ1 ζ2: Sub Exp) : Prop := *)
(*   { wrss_tyvar : ∀ {α k}, *)
(*                    ⟨ α ∷ k ∈ Γ ⟩ → *)
(*                    ⟨ Δ ⊢ ζγs α : ζ1 α ↝* ζ2 α ∷ k ⟩; *)
(*     wrss_covar : ∀ {c τ1 τ2 k}, *)
(*                    ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ → *)
(*                    ⟨ Δ ⊢ ζγs c : τ1[ζ1] ↝* τ2[ζ2] ∷ k ⟩; *)
(*     wrss_left :> ⟨ ζ1 : Γ => Δ ⟩; *)
(*     wrss_right :> ⟨ ζ2 : Γ => Δ ⟩; *)
(*   }. *)

(* Hint Resolve wrss_tyvar : ws. *)
(* Hint Resolve wrss_covar : ws. *)
(* Hint Resolve wrss_left : ws. *)
(* Hint Resolve wrss_right : ws. *)

(* Lemma wtRSSub_up_tyvar {Γ Δ ζγs ζ1 ζ2} (wζ: WtRSSub Γ Δ ζγs ζ1 ζ2) : *)
(*   ∀ k, WtRSSub (Γ ► k) (Δ ► k) (List.map upRedSub ζγs) ζ1↑ ζ2↑. *)
(* Proof. *)
(*   rewrite ?up_def. *)
(*   constructor; intros. *)
(*   - inversion H; clear H; crush. *)
(*     rewrite <- ?(ap_wkm_ix (X:=Exp)). *)
(*     crush. *)
(*   - inversion H; clear H; crush. *)
(*     rewrite ?ap_comp. *)
(*     rewrite ?wkm_snoc_cancel. *)
(*     rewrite <- ?ap_comp. *)
(*     rewrite <- ?(ap_wkm_ix (X:=Exp)). *)
(*     crush. *)
(*   - rewrite <- ?up_def; crush. *)
(*   - rewrite <- ?up_def; crush. *)
(* Qed. *)
(* Hint Resolve wtRedSub_up_tyvar : ws. *)

(* Lemma wtredsub_snoc_tyvar {Γ Δ ζγ ζ1 ζ2 γ σ τ k} : *)
(*   ⟨ Δ ⊢ γ : σ ↝ τ ∷ k ⟩ → ⟨ Δ ⊢ σ ∷ k ⟩ → ⟨ Δ ⊢ τ ∷ k ⟩ → *)
(*   WtRedSub Γ Δ ζγ ζ1 ζ2 → *)
(*   WtRedSub (Γ ► k) Δ (ζγ · γ) (ζ1 · σ) (ζ2 · τ). *)
(* Proof. *)
(*   intros; constructor; crush. *)
(*   rewrite ?ap_comp. *)
(*   rewrite ?wkm_snoc_cancel. *)
(*   crush. *)
(* Qed. *)

(* Lemma ty_redsub {Γ τ k} (wτ: ⟨ Γ ⊢ τ ∷ k ⟩) : *)
(*   ∀ Δ ζγ ζ1 ζ2, *)
(*     WtRedSub Γ Δ ζγ ζ1 ζ2 → *)
(*     ⟨ Δ ⊢ apRedSub ζγ τ : τ[ζ1] ↝ τ[ζ2] ∷ k ⟩. *)
(* Proof. induction wτ; crush. Qed. *)
(* Hint Resolve ty_redsub : ws. *)

(* Lemma red_redsub {Γ γ τ1 τ2 k} (wγ: ⟨ Γ ⊢ γ : τ1 ↝ τ2 ∷ k ⟩) : *)
(*   ∀ Δ ζγ ζ1 ζ2, *)
(*     WtRedSub Γ Δ ζγ ζ1 ζ2 → *)
(*     ⟨ Δ ⊢ apRedSub ζγ γ : τ1[ζ1] ↝ τ2[ζ2] ∷ k ⟩. *)
(* Proof. induction wγ; crush. Qed. *)
(* Hint Resolve red_redsub : ws. *)





Inductive DomBinding : Type :=
  | tyv
  | cov
  | tmv.

Definition Dom : Type := list DomBinding.

Definition domBinding (b: Binding) : DomBinding :=
  match b with
    | tyvar k => tyv
    | covar τ1 τ2 k => cov
    | tmvar τ => tmv
  end.

Definition dom (Γ: Env) : Dom :=
  List.map domBinding Γ.

Fixpoint coidm (D: Dom) : Sub Exp :=
  match D with
    | nil        => idm Exp
    | cons tyv D => (coidm D >=> wkm Exp) · corefl (var 0)
    | cons cov D => (coidm D >=> wkm Exp) · var 0
    | cons tmv D => (coidm D >=> wkm Exp) · var 0
  end.

Lemma coidm_covar {Γ c σ τ k} (wc: ⟨ c : σ ~ τ ∷ k ∈ Γ ⟩) :
  ⟨ Γ ⊢ coidm (dom Γ) c : σ ↝ τ ∷ k ⟩.
Proof.
  induction wc; crush.
  - rewrite <- ?(ap_wkm_ix (X:=Exp)).
    eapply red_ren; crush.
  - rewrite <- ?(ap_wkm_ix (X:=Exp)).
    eapply red_ren; crush.
  - rewrite <- ?(ap_wkm_ix (X:=Exp)).
    eapply red_ren; crush.
Qed.

Lemma wtredsub_idm Γ :
  WtRedSub Γ Γ (coidm (dom Γ)) (idm Exp) (idm Exp).
Proof.
  induction Γ.
  - constructor; crush.
    inversion H.
  - destruct a; crush.
    + rewrite <- up_idm, up_def.
      eapply wtredsub_snoc_tyvar; eauto with ws.
      constructor; crush.
      * rewrite <- ?(ap_wkm_ix (X:=Exp)).
        change (var (wk α)) with (var α)[wkm Ix].
        eapply red_ren; crush.
      * rewrite <- ?apply_wkm_comm, ?ap_id.
        rewrite <- ?(ap_wkm_ix (X:=Exp)).
        eapply red_ren; crush.
        apply coidm_covar; auto.
    + change (var 0) with (vr 0).
      rewrite <- up_def. constructor; crush.
      * change (var (S i)) with (var i)[wkm Ix].
        eapply red_ren; crush.
      * rewrite <- ?(ap_wkm_ix (X:=Exp)).
        eapply red_ren; crush.
        apply coidm_covar; auto.
    + constructor; crush.
      * rewrite <- ?(ap_wkm_ix (X:=Exp)).
        change (var (S i)) with (var i)[wkm Ix].
        eapply red_ren; crush.
      * rewrite <- ?(ap_wkm_ix (X:=Exp)).
        eapply red_ren; crush.
        apply coidm_covar; auto.
Qed.

Lemma wtRedSub_beta1 {Γ γ τ σ k} :
  ⟨ Γ ⊢ γ : σ ↝ τ ∷ k ⟩ →
  ⟨ Γ ⊢ σ ∷ k ⟩ →
  ⟨ Γ ⊢ τ ∷ k ⟩ →
  WtRedSub (Γ ► k) Γ (coidm (dom Γ) · γ) (beta1 σ) (beta1 τ).
Proof.
  intros wγ wσ wτ.
  destruct (wtredsub_idm Γ) as [coidm_tyvar coidm_covar coidm_left coidm_right].
  constructor; crush.
  replace τ0 with τ0[idm Exp] by apply ap_id.
  replace τ3 with τ3[idm Exp] by apply ap_id.
  eauto.
Qed.
Hint Resolve wtRedSub_beta1 : ws.

(* Lemma wtredsub_beta1 {Γ k γ σ τ} (wγ: ⟨ Γ ⊢ γ : σ ↝ τ ∷ k ⟩) : *)
(*   WtRedSub (Γ ► k) Γ (coidm · γ) (beta1 σ) (beta1 τ). *)
(* Proof. *)
(*   unfold beta1, beta. *)
(*   simpl snoc. *)
(*   apply wtredsub_snoc; eauto. *)
(*   admit. *)
(*   admit. *)
(*   c *)
(* Admitted. *)

(* Takahashi's complete developments adapted to coercions. *)
Fixpoint complete_ty (τ : Exp) : Exp :=
  match τ with
    | var α               => var α
    | τabs k τ            => τabs k (complete_ty τ)
    | τapp (τabs k τ1) τ2 => (complete_ty τ1)[beta1 (complete_ty τ2)]
    | τapp τ1 τ2          => τapp (complete_ty τ1) (complete_ty τ2)
    | arr τ1 τ2           => arr (complete_ty τ1) (complete_ty τ2)
    | arrτ k τ            => arrτ k (complete_ty τ)
    | arrγ τ1 τ2 k τ3     => arrγ (complete_ty τ1) (complete_ty τ2) k (complete_ty τ3)
    | _                   => τ
  end.

(* Definition ren_complete_ty τ : *)
(*   ∀ (ξ: Sub Ix), complete_ty τ[ξ] = (complete_ty τ)[ξ]. *)
(* Proof. *)
(*   enough *)
(*     ((∀ (ξ: Sub Ix), *)
(*         complete_ty τ[ξ] = (complete_ty τ)[ξ]) ∧ *)
(*      (∀ (τ2 : Exp) (ξ : Sub Ix), *)
(*         complete_ty τ2[ξ] = (complete_ty τ2)[ξ] → *)
(*         complete_ty (τapp τ τ2)[ξ] = (complete_ty (τapp τ τ2))[ξ])) as []; auto. *)
(*   induction τ; split; try (crush; intuition; crush; fail). *)
(*   intros; cbn. *)
(*   destruct IHτ. *)
(*   repeat crushSyntaxRefold. *)
(*   rewrite H0, H. *)
(*   rewrite <- ?ap_liftSub. *)
(*   rewrite apply_beta1_comm. *)
(*   rewrite up_liftSub. *)
(*   reflexivity. *)
(* Qed. *)

Fixpoint complete_ty_co (τ: Exp) : Exp :=
  match τ with
    | var α               => corefl (var α)
    | τabs k τ            => coτabs k (complete_ty_co τ)
    | τapp (τabs k τ1) τ2 => cobeta k (complete_ty_co τ1) (complete_ty_co τ2)
    | τapp τ1 τ2          => coτapp (complete_ty_co τ1) (complete_ty_co τ2)
    | arr τ1 τ2           => coarr (complete_ty_co τ1) (complete_ty_co τ2)
    | arrτ k τ            => coarrτ k (complete_ty_co τ)
    | arrγ τ1 τ2 k τ3     => coarrγ (complete_ty_co τ1) (complete_ty_co τ2) k (complete_ty_co τ3)
    | _                   => cast (var 1) (var 1)
  end.

Fixpoint complete_co (D: Dom) (γ : Exp) : Exp :=
  match γ with
    | var c                         => var c
    | coτabs k γ                    => coτabs k (complete_co (cons tyv D) γ)
    | coτapp (coτabs k γ1) γ2       => cobeta k (complete_co (cons tyv D) γ1) (complete_co D γ2)
    (* | coτapp (corefl (τabs k τ)) γ2 => cobeta (complete_ty_co τ) (complete_co γ2) *)
    | coτapp γ1 γ2                  => coτapp (complete_co D γ1) (complete_co D γ2)
    | coarr γ1 γ2                   => coarr (complete_co D γ1) (complete_co D γ2)
    | coarrτ k γ                    => coarrτ k (complete_co (cons tyv D) γ)
    | coarrγ γ1 γ2 k γ3             => coarrγ (complete_co D γ1) (complete_co D γ2) k (complete_co D γ3)
    | cobeta k γ1 γ2                => apRedSub (coidm D · complete_co D γ2) (complete_co (cons tyv D) γ1)
    | corefl τ                      => complete_ty_co τ
    | _ => cast (var 2) (var 2)
  end.

Lemma complete_ty_co_sound {Γ τ k} (wτ: ⟨ Γ ⊢ τ ∷ k ⟩) :
  ⟨ Γ ⊢ complete_ty_co τ : τ ↝ complete_ty τ ∷ k ⟩.
Proof.
  induction wτ; crush.
  inversion wτ1; crush.
Qed.

Lemma complete_co_triangle {Γ γ σ τ k} (r: ⟨ Γ ⊢ γ : σ ↝ τ ∷ k ⟩)
  (wΓ: WfEnv Γ) (clΓ: CoVarClosed Γ) :
  ⟨ Γ ⊢ complete_co (dom Γ) γ : τ ↝ complete_ty σ ∷ k ⟩.
Proof.
  induction r; crush;
    eauto 20 using red_co, co_agreement_right,
    wtredsub_idm, wtredsub_snoc_tyvar, red_redsub with ws.
  - inversion r1; crush.
Qed.

Lemma red_diamond {Γ σ γ η τ ν k} (wΓ: WfEnv Γ) (clΓ: CoVarClosed Γ)
  (wγ: ⟨ Γ ⊢ γ : σ ↝ τ ∷ k ⟩)
  (wη: ⟨ Γ ⊢ η : σ ↝ ν ∷ k ⟩) :
  ∃ υ,
    (∃ η', ⟨ Γ ⊢ η' : τ ↝ υ ∷ k ⟩) ∧
    (∃ γ', ⟨ Γ ⊢ γ' : ν ↝ υ ∷ k ⟩).
Proof.
  exists (complete_ty σ); split.
  - exists (complete_co (dom Γ) γ).
    eauto using complete_co_triangle.
  - exists (complete_co (dom Γ) η).
    eauto using complete_co_triangle.
Qed.

Lemma red_strip {Γ γs η σ τ ν k}
  (wΓ: WfEnv Γ) (clΓ: CoVarClosed Γ)
  (wγs: ⟨ Γ ⊢ γs : σ ↝* τ ∷ k ⟩)
  (wη:  ⟨ Γ ⊢ η : σ ↝ ν ∷ k ⟩) :
  ∃ υ,
    (∃ η',  ⟨ Γ ⊢ η'  : τ ↝  υ ∷ k ⟩) ∧
    (∃ γs', ⟨ Γ ⊢ γs' : ν ↝* υ ∷ k ⟩).
Proof.
  induction wγs as [|σ τ τ' γs γ k wγs IHwγs wγ]; cbn.
  - exists ν; split.
    + exists η; crush.
    + exists nil; crush;
        eauto using red_co, co_agreement_right with ws.
  - (*      γs       γ
         σ   →   τ   →   τ'

       η ↓       ⇣η'      ⇣η''

         ν   →   υ   →   υ'
            γs'      γ'
    *)
    destruct (IHwγs wη) as (υ & (η' & wη') & (γs' & wγs')).
    destruct (red_diamond wΓ clΓ wγ wη') as (υ' & (η'' & wη'') & (γ' & wγ')).
    exists υ'.
    split.
    + exists η''; eauto with ws.
    + exists (cons γ' γs'); eauto with ws.
Qed.

Lemma red_confluence {Γ γs ηs σ τ ν k}
  (wΓ: WfEnv Γ) (clΓ: CoVarClosed Γ)
  (wγs: ⟨ Γ ⊢ γs : σ ↝* τ ∷ k ⟩)
  (wηs: ⟨ Γ ⊢ ηs : σ ↝* ν ∷ k ⟩) :
  ∃ υ,
    (∃ ηs', ⟨ Γ ⊢ ηs' : τ ↝* υ ∷ k ⟩) ∧
    (∃ γs', ⟨ Γ ⊢ γs' : ν ↝* υ ∷ k ⟩).
Proof.
  induction wγs as [|σ τ τ' γs γ k wγs IHwγs wγ]; cbn.
  - exists ν; split.
    + exists ηs; crush.
    + exists nil; crush;
        eauto using redstar_co, co_agreement_right with ws.
  - specialize (IHwγs wηs).
    destruct IHwγs as (υ & (ηs' & wηs') & (γs' & wγs')).
    destruct (red_strip wΓ clΓ wηs' wγ) as (υ' & (γ' & wγ') & (ηs'' & wηs'')).
    exists υ'; split.
    + exists ηs''; eauto with ws.
    + exists (cons γ' γs'); eauto with ws.
Qed.

Definition rssubst₁ (Γ: Env) (σγs: list Exp) (τ: Exp) : list Exp :=
   List.map (apRedSub (coidm (dom Γ) · redrefl τ)) σγs.
Definition rssubst₂ (Γ: Env) (σ: Exp) (τγs: list Exp) : list Exp :=
   List.map (fun γ => apRedSub (coidm (dom Γ) · γ) σ) τγs.
Definition rssubst (Γ: Env) (σγs: list Exp) (σ1 σ2: Exp) (τγs: list Exp) (τ1 τ2 : Exp) : list Exp :=
  rstrans (rssubst₁ Γ σγs τ1) (rssubst₂ Γ σ2 τγs).

Lemma RsSubst₁ {Γ σγs σ σ' τ k1 k2} (wΓ: WfEnv Γ) :
  ⟨ Γ ► k1 ⊢ σγs : σ ↝* σ' ∷ k2 ⟩ →
  ⟨ Γ ⊢ τ ∷ k1 ⟩ →
  ⟨ Γ ⊢ rssubst₁ Γ σγs τ : σ[beta1 τ] ↝* σ'[beta1 τ] ∷ k2 ⟩.
Proof. intros wσγs; depind wσγs; crush. Qed.
Lemma RsSubst₂ {Γ σ τγs τ τ' k1 k2} (wΓ: WfEnv Γ) :
  ⟨ Γ ► k1 ⊢ σ ∷ k2 ⟩ →
  ⟨ Γ ⊢ τγs : τ ↝* τ' ∷ k1 ⟩ →
  ⟨ Γ ⊢ rssubst₂ Γ σ τγs : σ[beta1 τ] ↝* σ[beta1 τ'] ∷ k2 ⟩.
Proof.
  intros wσ wτγs; depind wτγs; crush;
  eauto 20 using red_co, co_agreement_right,
    wtredsub_idm, wtredsub_snoc_tyvar, red_redsub with ws.
Qed.
Lemma RsSubst {Γ σγs σ σ' τγs τ τ' k1 k2} (wΓ: WfEnv Γ) :
  ⟨ Γ ► k1 ⊢ σγs : σ ↝* σ' ∷ k2 ⟩ →
  ⟨ Γ ⊢ τγs : τ ↝* τ' ∷ k1 ⟩ →
  ⟨ Γ ⊢ rssubst Γ σγs σ σ' τγs τ τ' : σ[beta1 τ] ↝* σ'[beta1 τ'] ∷ k2 ⟩.
Proof.
  intros.
  eapply RsTrans.
  - eapply RsSubst₁; crush; eauto using redstar_co, co_agreement_left with ws.
  - eapply RsSubst₂; crush; eauto using redstar_co, co_agreement_right with ws.
Qed.

Lemma co_red {Γ γ σ τ k} (wγ : ⟨ Γ ⊢ γ : σ ~ τ ∷ k⟩)
  (wΓ: WfEnv Γ) (clΓ: CoVarClosed Γ) :
  ∃ υ,
    (∃ ηs, ⟨ Γ ⊢ ηs : τ ↝* υ ∷ k ⟩) ∧
    (∃ γs, ⟨ Γ ⊢ γs : σ ↝* υ ∷ k ⟩).
Proof.
  induction wγ; cbn; crushIH.
  - elimtype False; eapply clΓ; eauto.
  - destruct IHwγ as (υ & (ηs & wηs) & (γs & wγs)).
    exists (τabs k1 υ); split.
    + exists (rsτabs k1 ηs); eauto using RsTAbs.
    + exists (rsτabs k1 γs); eauto using RsTAbs.
  - destruct IHwγ1 as (υ1 & (γs21 & wγ21) & (γs11 & wγ11)).
    destruct IHwγ2 as (υ2 & (γs22 & wγ22) & (γs12 & wγ12)).
    exists (τapp υ1 υ2); split.
    + exists (rsτapp γs21 τ21 υ1 γs22 τ22 υ2).
      eapply RsTApp; crush; eauto using redstar_co, co_agreement_right.
    + exists (rsτapp γs11 τ11 υ1 γs12 τ12 υ2).
      eapply RsTApp; crush; eauto using redstar_co, co_agreement_left, co_agreement_right.
  - destruct IHwγ1 as (υ1 & (γs21 & wγ21) & (γs11 & wγ11)).
    destruct IHwγ2 as (υ2 & (γs22 & wγ22) & (γs12 & wγ12)).
    exists (arr υ1 υ2); split.
    + exists (rsarr γs21 τ21 υ1 γs22 τ22 υ2).
      eapply RsArr; crush; eauto using redstar_co, co_agreement_right.
    + exists (rsarr γs11 τ11 υ1 γs12 τ12 υ2).
      eapply RsArr; crush; eauto using redstar_co, co_agreement_left, co_agreement_right.
  - destruct IHwγ as (υ & (ηs & wηs) & (γs & wγs)).
    exists (arrτ k υ); split.
    + exists (rsarrτ k ηs).
      eapply RsArrT; eauto.
    + exists (rsarrτ k γs).
      eapply RsArrT; eauto.
  - destruct IHwγ1 as (υ1 & (γs1' & wγs1') & (γs1 & wγs1)).
    destruct IHwγ2 as (υ2 & (γs2' & wγs2') & (γs2 & wγs2)).
    destruct IHwγ3 as (υ3 & (γs3' & wγs3') & (γs3 & wγs3)).
    exists (arrγ υ1 υ2 k υ3); split.
    + exists (rsarrγ γs1' τ1' υ1 γs2' τ2' υ2 k γs3' τ3' υ3).
      eapply RsArrG; crush; eauto using redstar_co, co_agreement_left, co_agreement_right.
    + exists (rsarrγ γs1 τ1 υ1 γs2 τ2 υ2 k γs3 τ3 υ3).
      eapply RsArrG; crush; eauto using redstar_co, co_agreement_left, co_agreement_right.
  - destruct IHwγ as (? & (? & wηs) & (? & wγs)).
    apply arr_consistency in wγs; eauto.
    apply arr_consistency in wηs; eauto.
    crush.
  - destruct IHwγ as (? & (? & wηs) & (? & wγs)).
    apply arr_consistency in wγs; eauto.
    apply arr_consistency in wηs; eauto.
    crush.
  - destruct IHwγ1 as (υ & (ηs & wηs) & (γs & wγs)).
    apply arrτ_consistency in wγs; eauto.
    apply arrτ_consistency in wηs; eauto.
    destruct wγs as (υ1  & Heq1 & (γs1 & wγs1)).
    destruct wηs as (υ1' & Heq2 & (γs2 & wγs2)).
    destruct IHwγ2 as (υ2 & (ηs' & wηs') & (γs' & wγs')).
    exists (υ1[beta1 υ2]); split.
    + exists (rssubst Γ γs2 τ2 υ1 ηs' τ4 υ2).
      eapply RsSubst; crush.
    + exists (rssubst Γ γs1 τ1 υ1 γs' τ3 υ2).
      eapply RsSubst; crush.
  - destruct IHwγ as (υ & (ηs & wηs) & (γs & wγs)).
    apply arrγ_consistency in wγs; eauto.
    apply arrγ_consistency in wηs; eauto.
    crush.
  - destruct IHwγ as (υ & (ηs & wηs) & (γs & wγs)).
    apply arrγ_consistency in wγs; eauto.
    apply arrγ_consistency in wηs; eauto.
    crush.
  - destruct IHwγ as (υ & (ηs & wηs) & (γs & wγs)).
    apply arrγ_consistency in wγs; eauto.
    apply arrγ_consistency in wηs; eauto.
    crush.
  - destruct IHwγ1 as (υ1 & (γs1' & wγs1') & (γs1 & wγs1)).
    destruct IHwγ2 as (υ2 & (γs2' & wγs2') & (γs2 & wγs2)).
    exists (υ1[beta1 υ2]); split.
    + exists (rssubst Γ γs1' τ1' υ1 γs2' τ2' υ2).
      eapply RsSubst; crush.
    + exists (rsbeta k1 γs1 τ1 υ1 γs2 τ2 υ2); eapply RsBeta; crush;
        eauto using redstar_co, co_agreement_left, co_agreement_right with ws.
  - exists τ; split.
    + exists nil; crush.
    + exists nil; crush.
  - crush.
  - destruct IHwγ1 as (υl & (γsl1 & wγsl1) & (γsl2 & wγsl2)).
    destruct IHwγ2 as (υr & (γsr1 & wγsr1) & (γsr2 & wγsr2)).
    destruct (red_confluence wΓ clΓ wγsl1 wγsr2) as (υ & (ηsl & wηsl) & (ηsr & wηsr)).
    exists υ; split.
    + exists (rstrans γsr1 ηsr).
      eapply RsTrans; crush.
    + exists (rstrans γsl2 ηsl).
      eapply RsTrans; crush.
Qed.




(* Lemma red_ren {Γ γ τ1 τ2 k} (wγ: ⟨ Γ ⊢ γ : τ1 ↝ τ2 ∷ k ⟩) : *)
(*   ∀ Δ ζ, ⟨ ζ : Γ -> Δ ⟩ → ⟨ Δ ⊢ γ[ζ] : τ1[ζ] ↝ τ2[ζ] ∷ k ⟩. *)
(* Proof. *)
(*   induction wγ; intros ? ζ wζ; crush. *)
(*   - rewrite <- ?ap_liftSub. *)
(*     rewrite ?apply_beta1_comm. *)
(*     rewrite ?up_liftSub. *)
(*     rewrite ?ap_liftSub. *)
(*     econstructor; eauto with ws. *)
(*   - rewrite <- ?ap_liftSub. *)
(*     rewrite ?apply_beta1_comm. *)
(*     rewrite ?up_liftSub. *)
(*     rewrite ?ap_liftSub. *)
(*     econstructor; eauto with ws. *)
(* Qed. *)
(* Hint Resolve co_ren : ws. *)

(* Record WtRedSub (Γ Δ: Env) (ζγ ζγi ζ1 ζ2: Sub Exp) : Prop := *)
(*   { wrs_tyvar : ∀ {α k}, *)
(*                   ⟨ α ∷ k ∈ Γ ⟩ → *)
(*                   ⟨ Δ ⊢ ζγ α : ζ1 α ↝ ζ2 α ∷ k ⟩; *)
(*     wrs_covar : ∀ {c τ1 τ2 k}, *)
(*                   ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ → *)
(*                   ⟨ Δ ⊢ ζγ c : τ1[ζ1] ↝ τ2[ζ2] ∷ k ⟩; *)
(*     wrs_tyvari : ∀ {α k}, *)
(*                   ⟨ α ∷ k ∈ Γ ⟩ → *)
(*                   ⟨ Δ ⊢ ζγi α : ζ2 α ↝ ζ1 α ∷ k ⟩; *)
(*     wrs_covari : ∀ {c τ1 τ2 k}, *)
(*                   ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ → *)
(*                   ⟨ Δ ⊢ ζγi c : τ1[ζ2] ↝ τ2[ζ1] ∷ k ⟩; *)
(*     wrs_left :> ⟨ ζ1 : Γ => Δ ⟩; *)
(*     wrs_right :> ⟨ ζ2 : Γ => Δ ⟩; *)
(*   }. *)

(* Hint Resolve wrs_covar : ws. *)
(* Hint Resolve wrs_tyvari : ws. *)
(* Hint Resolve wrs_covari : ws. *)
(* Hint Resolve wrs_left : ws. *)
(* Hint Resolve wrs_right : ws. *)
(* Hint Constructors Red : ws. *)

(* Lemma wtRedSub_up_tyvar {Γ Δ ζγ ζγi ζ1 ζ2} (wζ: WtRedSub Γ Δ ζγ ζγi ζ1 ζ2) : *)
(*   ∀ k, WtRedSub (Γ ► k) (Δ ► k) (upRedSub ζγ) (upRedSub ζγi) ζ1↑ ζ2↑. *)
(* Proof. *)
(*   rewrite ?up_def. *)
(*   constructor; intros. *)
(*   - inversion H; clear H; crush. *)
(*   - inversion H; clear H; crush. *)
(*     rewrite ?ap_comp. *)
(*     rewrite ?wkm_snoc_cancel. *)
(*     rewrite <- ?ap_comp. *)
(*     rewrite <- ?(ap_wkm_ix (X:=Exp)). *)
(*     crush. *)
(*   - inversion H; clear H; crush. *)
(*   - inversion H; clear H; crush. *)
(*     rewrite ?ap_comp. *)
(*     rewrite ?wkm_snoc_cancel. *)
(*     rewrite <- ?ap_comp. *)
(*     rewrite <- ?(ap_wkm_ix (X:=Exp)). *)
(*     crush. *)
(*   - rewrite <- ?up_def; crush. *)
(*   - rewrite <- ?up_def; crush. *)
(* Qed. *)
(* Hint Resolve wtCoSub_up_tyvar : ws. *)
