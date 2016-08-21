Require Import Coq.Lists.List.
Require Export ParDB.Spec.
Require Export ParDB.Lemmas.
Require Export ParDB.Inst.

Require Export SpecSyntax.
Require Export SpecTyping.

Arguments wkm _ {_ _} _.
Arguments comp _ _ {_ _ } _ _ _.

Record WtRen (Γ Δ: Env) (ζ: Sub Ix) : Prop :=
  { wtr_tyvar : ∀ {α k},
                  ⟨ α ∷ k ∈ Γ ⟩ →
                  ⟨ ζ α ∷ k ∈ Δ ⟩;
    wtr_covar : ∀ {c τ1 τ2 k},
                  ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ →
                  ⟨ ζ c : τ1[ζ] ~ τ2[ζ] ∷ k ∈ Δ ⟩;
    wtr_tmvar : ∀ {x τ},
                  ⟨ x : τ ∈ Γ ⟩ →
                  ⟨ ζ x : τ[ζ] ∈ Δ ⟩
  }.

Notation "⟨ ζ : Γ -> Δ ⟩" := (WtRen Γ Δ ζ)
  (at level 0,
   ζ at level 98,
   Γ at level 98,
   Δ at level 98).

Arguments wtr_tyvar {_ _ _} _ {_ _} _.
Arguments wtr_covar {_ _ _} _ {_ _ _ _} _.
Arguments wtr_tmvar {_ _ _} _ {_ _} _.

Record WtSub (Γ Δ: Env) (ζ: Sub Exp) : Prop :=
  { wts_tyvar : ∀ {α k},
                  ⟨ α ∷ k ∈ Γ ⟩ →
                  ⟨ Δ ⊢ ζ α ∷ k ⟩;
    wts_covar : ∀ {c τ1 τ2 k},
                  ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ →
                  ⟨ Δ ⊢ ζ c : τ1[ζ] ~ τ2[ζ] ∷ k ⟩;
    wts_tmvar : ∀ {x τ},
                  ⟨ x : τ ∈ Γ ⟩ →
                  ⟨ Δ ⊢ ζ x : τ[ζ] ⟩;
  }.
Notation "⟨ ζ : Γ => Δ ⟩" := (WtSub Γ Δ ζ)
  (at level 0, ζ at level 98, Γ at level 98, Δ at level 98).

Arguments wts_tyvar {_ _ _} _ {_ _} _.
Arguments wts_covar {_ _ _} _ {_ _ _ _} _.
Arguments wts_tmvar {_ _ _} _ {_ _} _.

Hint Constructors Ty : ws.
Hint Constructors Co : ws.
Hint Constructors Red : ws.
Hint Constructors RedStar : ws.
Hint Constructors Tm : ws.
Hint Resolve wtr_tyvar : ws.
Hint Resolve wtr_covar : ws.
Hint Resolve wtr_tmvar : ws.
Hint Resolve wts_tyvar : ws.
Hint Resolve wts_covar : ws.
Hint Resolve wts_tmvar : ws.

(* Lemma getEvarInvHere { Γ T U } : *)
(*   ⟪ 0 : T ∈ (Γ ▻ U) ⟫ → T = U. *)
(* Proof. inversion 1; auto. Qed. *)

(* Lemma getEvarInvThere {Γ i T U} : *)
(*   ⟪ (S i) : T ∈ Γ ▻ U ⟫ → ⟪ i : T ∈ Γ ⟫. *)
(* Proof. inversion 1; auto. Qed. *)
(* Hint Resolve getEvarInvThere : wsi. *)

Ltac crushTypingMatchH :=
  match goal with
    | [H: ⟨ 0 : _ ∈ _ ⟩                    |- _] => inversion H; clear H; subst*
    | [H: ⟨ (S _) : _ ∈ _ ⟩                |- _] => inversion H; clear H; subst*
    | [H: ⟨ 0 ∷ _ ∈ _ ⟩                    |- _] => inversion H; clear H; subst*
    | [H: ⟨ (S _) ∷ _ ∈ _ ⟩                |- _] => inversion H; clear H; subst*
    | [H: ⟨ 0 : _ ~ _ ∷ _ ∈ _ ⟩            |- _] => inversion H; clear H; subst*
    | [H: ⟨ (S _) : _ ~ _ ∷ _ ∈ _ ⟩        |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ : _ ∈ nil ⟩                  |- _] => inversion H; clear H; subst*
    (* Ty *)
    | [H: ⟨ _ ⊢ var _ ∷ _ ⟩                |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ τabs _ _ ∷ _ ⟩             |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ τapp _ _ ∷ _ ⟩             |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ arr _ _ ∷ _ ⟩              |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ arrτ _ _ ∷ _ ⟩             |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ arrγ _ _ _ _ ∷ _ ⟩         |- _] => inversion H; clear H; subst*
    (* Co *)
    | [H: ⟨ _ ⊢ var _          : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ coτabs _ _     : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ coτapp _ _     : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ coarr _ _      : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ coarrτ _ _     : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ coarrγ _ _ _ _ : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ coinvarr₁ _    : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ coinvarr₂ _    : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ coinvarrτ _ _  : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ coinvarrγ₁ _   : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ coinvarrγ₂ _   : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ coinvarrγ₂ _   : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ cobeta _ _ _   : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ corefl _       : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ cosym _        : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ cotrans _ _    : _ ~ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    (* Red *)
    | [H: ⟨ _ ⊢ var _ : _ ↝ _ ∷ _ ⟩        |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ coτabs _ _ : _ ↝ _ ∷ _ ⟩   |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ _ : arr _ _ ↝ _ ∷ _ ⟩      |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ _ : arrτ _ _ ↝ _ ∷ _ ⟩     |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ _ : arrγ _ _ _ _ ↝ _ ∷ _ ⟩ |- _] => inversion H; clear H; subst*
    (* Tm *)
    | [H: ⟨ _ ⊢ var _ : _        ⟩         |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ abs _ _ : _      ⟩         |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ absτ _ _ : _     ⟩         |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ absγ _ _ _ _ : _ ⟩         |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ app _ _ : _      ⟩         |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ appτ _ _ : _     ⟩         |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ appγ _ _ : _     ⟩         |- _] => inversion H; clear H; subst*
    | [H: ⟨ _ ⊢ cast _ _ : _     ⟩         |- _] => inversion H; clear H; subst*

    (* | [ wi : ⟪ ?i : _ ∈ (_ ▻ _) ⟫ *)
    (*     |- context [match ?i with _ => _ end] *)
    (*   ] => destruct i *)
    | [ wi : ⟨ ?i : _ ∈ (_ ▻ _) ⟩ |- _] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i ∷ _ ∈ (_ ▻ _) ⟩ |- _] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i : _ ~ _ ∷ _ ∈ (_ ▻ _) ⟩ |- _] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i : _ ∈ (_ ► _) ⟩ |- _] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i ∷ _ ∈ (_ ► _) ⟩ |- _] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i : _ ~ _ ∷ _ ∈ (_ ► _) ⟩ |- _] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i : _ ∈ (_ ◅ _ ~ _ ∷ _) ⟩ |- _] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i ∷ _ ∈ (_ ◅ _ ~ _ ∷ _) ⟩ |- _] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i : _ ~ _ ∷ _ ∈ (_ ► _) ⟩ |- _] => inversion wi; clear wi
    | [ wi : ⟨ ?i : _ ~ _ ∷ _ ∈ (_ ◅ _ ~ _ ∷ _) ⟩ |- _] => destruct i eqn: ?; cbn in *

    | [ |- ⟨ _ ⊢ (_ :: _) : _ ↝* _ ∷ _ ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ nil : _ ↝* _ ∷ _ ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ coarrγ _ _ _ _ : _ ↝ _ ∷ _ ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ _ : arrγ _ _ _ _ ↝ _ ∷ _ ⟩ ] => econstructor
    | [ |- ⟨ _ ⊢ cotrans _ _ : _ ~ _ ∷ _ ⟩ ] => econstructor

    (* | [ wi : ⟨ ?i : _ ∈ (_ ► _) ⟩ *)
    (*     |- context [(_ · _) ?i] *)
    (*   ] => destruct i eqn: ?; cbn in * *)
    (* | [ wi : ⟨ ?i : _ ∈ (_ ◅ _ ~ _ ∷ _) ⟩ *)
    (*     |- context [(_ · _) ?i] *)
    (*   ] => destruct i eqn: ?; cbn in * *)
    (* | [ |- ⟪ _ ⊢ var _ : _ ⟫         ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ abs _ _ : _ ⟫       ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ app _ _ : _ ⟫       ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ unit : _ ⟫          ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ true : _ ⟫          ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ false : _ ⟫         ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ ite _ _ _ : _ ⟫     ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ pair _ _ : _ ⟫      ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ proj₁ _ : _ ⟫       ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ proj₂ _ : _ ⟫       ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ inl _ : _ ⟫         ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ inr _ : _ ⟫         ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ caseof _ _ _ : _ ⟫  ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ seq _ _ : _ ⟫       ] => econstructor *)
    (* | [ |- ⟪ _ ⊢ fixt _ _ _ : _ ⟫    ] => econstructor *)
  end.

Hint Constructors GetTyVar : ws.
Hint Constructors GetCoVar : ws.
Hint Constructors GetTmVar : ws.

Local Ltac crush :=
  intros;
  repeat
    (cbn in *;
     repeat crushSyntaxMatch;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasRewriteH;
     repeat crushSyntaxRefold;
     (* repeat crushTypingMatchH; *)
     subst*;
     try discriminate;
     eauto 200 with core ws;
     idtac
    ).

(*************************************************************************)

Lemma wtRen_closed {ζ Δ} :
  ⟨ ζ : nil -> Δ ⟩.
Proof. constructor; inversion 1. Qed.
Hint Resolve wtRen_closed : ws.

Lemma wtRen_idm Γ :
  ⟨ idm Ix : Γ -> Γ ⟩.
Proof. constructor; crush. Qed.
Hint Resolve wtRen_idm : ws.

Lemma wtRen_comp {Γ₁ Γ₂ Γ₃ ξ₁ ξ₂} :
  ⟨ ξ₁ : Γ₁ -> Γ₂ ⟩ →
  ⟨ ξ₂ : Γ₂ -> Γ₃ ⟩ →
  ⟨ ξ₁ >=> ξ₂ : Γ₁ -> Γ₃ ⟩.
Proof. constructor; crush. Qed.
Hint Resolve wtRen_comp : ws.

(*************************************************************************)

Lemma wtRen_wkm_tyvar Γ k :
  ⟨ wkm Ix : Γ -> Γ ► k ⟩.
Proof. constructor; intros; rewrite ?ap_wkm_ix; crush. Qed.
Hint Resolve wtRen_wkm_tyvar : ws.

Lemma wtRen_wkm_covar Γ τ1 τ2 k :
  ⟨ wkm Ix : Γ -> Γ ◅ τ1 ~ τ2 ∷ k ⟩.
Proof. constructor; intros; rewrite ?ap_wkm_ix; crush. Qed.
Hint Resolve wtRen_wkm_covar : ws.

Lemma wtRen_wkm_tmvar Γ τ :
  ⟨ wkm Ix : Γ -> Γ ▻ τ ⟩.
Proof. constructor; intros; rewrite ?ap_wkm_ix; crush. Qed.
Hint Resolve wtRen_wkm_tmvar : ws.

Lemma wtRen_snoc_tyvar {Γ Δ ζ α k} :
  ⟨ ζ : Γ -> Δ ⟩ →
  ⟨ α ∷ k ∈ Δ ⟩ →
  ⟨ ζ · α : Γ ► k -> Δ ⟩.
Proof.
  intros wζ wx; constructor; crush; repeat crushTypingMatchH;
    rewrite <- ?ap_wkm_ix, ?ap_comp, ?wkm_snoc_cancel; crush.
Qed.
Hint Resolve wtRen_snoc_tyvar : ws.

Lemma wtRen_snoc_covar {Γ Δ ζ c τ1 τ2 k} :
  ⟨ ζ : Γ -> Δ ⟩ →
  ⟨ c : τ1[ζ] ~ τ2[ζ] ∷ k ∈ Δ ⟩ →
  ⟨ ζ · c : Γ ◅ τ1 ~ τ2 ∷ k -> Δ ⟩.
Proof.
  intros wζ wx; constructor; crush; repeat crushTypingMatchH;
    rewrite <- ?ap_wkm_ix, ?ap_comp, ?wkm_snoc_cancel; crush.
Qed.
Hint Resolve wtRen_snoc_covar : ws.

Lemma wtRen_snoc_tmvar {Γ Δ ζ x τ} :
  ⟨ ζ : Γ -> Δ ⟩ →
  ⟨ x : τ[ζ] ∈ Δ ⟩ →
  ⟨ ζ · x : Γ ▻ τ -> Δ ⟩.
Proof.
  intros wζ wx; constructor; crush; repeat crushTypingMatchH;
    rewrite <- ?ap_wkm_ix, ?ap_comp, ?wkm_snoc_cancel; crush.
Qed.
Hint Resolve wtRen_snoc_tmvar : ws.

Lemma wtRen_up_tyvar {Γ₁ Γ₂ ζ} (wζ: ⟨ ζ : Γ₁ -> Γ₂ ⟩) :
  ∀ k, ⟨ ζ↑ : Γ₁ ► k -> Γ₂ ► k ⟩.
Proof. rewrite up_def. constructor; crush. Qed.
Hint Resolve wtRen_up_tyvar : ws.

Lemma wtRen_up_covar {Γ₁ Γ₂ ζ} (wζ: ⟨ ζ : Γ₁ -> Γ₂ ⟩) :
  ∀ τ1 τ2 k, ⟨ ζ↑ : Γ₁ ◅ τ1 ~ τ2 ∷ k -> Γ₂ ◅ τ1[ζ] ~ τ2[ζ] ∷ k ⟩.
Proof.
  rewrite up_def.
  constructor; crush.
  - inversion H; clear H; crush.
  - inversion H; clear H; crush.
    + rewrite <- ?(ap_wkm_ix (X:=Exp)), ?ap_comp.
      rewrite ?wkm_snoc_cancel.
      rewrite <- ?ap_comp, ?(ap_wkm_ix (X:=Exp)).
      constructor.
    + rewrite <- ?(ap_wkm_ix (X:=Exp)), ?ap_comp.
      rewrite ?wkm_snoc_cancel.
      rewrite <- ?ap_comp, ?(ap_wkm_ix (X:=Exp)).
      constructor.
      now apply (wtr_covar wζ).
  - inversion H; clear H; crush.
    rewrite <- (ap_wkm_ix (X:=Exp)), ap_comp.
    rewrite wkm_snoc_cancel.
    rewrite <- ap_comp, (ap_wkm_ix (X:=Exp)).
    constructor.
    now apply (wtr_tmvar wζ).
Qed.
Hint Resolve wtRen_up_covar : ws.

Lemma wtRen_up_tmvar {Γ₁ Γ₂ ζ} (wζ: ⟨ ζ : Γ₁ -> Γ₂ ⟩) :
  ∀ τ, ⟨ ζ↑ : Γ₁ ▻ τ -> Γ₂ ▻ τ[ζ] ⟩.
Proof.
  rewrite up_def.
  constructor; crush.
  - inversion H; clear H; crush.
  - inversion H; clear H; crush.
    rewrite <- ?(ap_wkm_ix (X:=Exp)), ?ap_comp.
    rewrite ?wkm_snoc_cancel.
    rewrite <- ?ap_comp, ?(ap_wkm_ix (X:=Exp)).
    constructor.
    now apply (wtr_covar wζ).
  - inversion H; clear H; crush.
    + rewrite <- ap_wkm_ix, ap_comp.
      rewrite wkm_snoc_cancel.
      rewrite <- ap_comp, ap_wkm_ix.
      constructor.
    + rewrite <- (ap_wkm_ix (X:=Exp)) , ap_comp.
      rewrite wkm_snoc_cancel.
      rewrite <- ap_comp, (ap_wkm_ix (X:=Exp)).
      constructor.
      now apply (wtr_tmvar wζ).
Qed.
Hint Resolve wtRen_up_tmvar : ws.

Lemma ty_ren {Γ τ k} (wτ: ⟨ Γ ⊢ τ ∷ k ⟩) :
  ∀ Δ ζ, ⟨ ζ : Γ -> Δ ⟩ → ⟨ Δ ⊢ τ[ζ] ∷ k ⟩.
Proof. induction wτ; crush. Qed.
Hint Resolve ty_ren : ws.

Lemma co_ren {Γ γ τ1 τ2 k} (wγ: ⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ k ⟩) :
  ∀ Δ ζ, ⟨ ζ : Γ -> Δ ⟩ → ⟨ Δ ⊢ γ[ζ] : τ1[ζ] ~ τ2[ζ] ∷ k ⟩.
Proof.
  induction wγ; intros ? ζ wζ; crush.
  - rewrite <- ?ap_liftSub.
    rewrite ?apply_beta1_comm.
    rewrite ?up_liftSub.
    rewrite ?ap_liftSub.
    econstructor; eauto with ws.
  - rewrite <- ?ap_liftSub.
    rewrite ?apply_beta1_comm.
    rewrite ?up_liftSub.
    rewrite ?ap_liftSub.
    econstructor; eauto with ws.
Qed.
Hint Resolve co_ren : ws.

Lemma red_ren {Γ γ τ1 τ2 k} (wγ: ⟨ Γ ⊢ γ : τ1 ↝ τ2 ∷ k ⟩) :
  ∀ Δ ζ, ⟨ ζ : Γ -> Δ ⟩ → ⟨ Δ ⊢ γ[ζ] : τ1[ζ] ↝ τ2[ζ] ∷ k ⟩.
Proof.
  induction wγ; intros ? ζ wζ; crush.
  - rewrite <- ?ap_liftSub.
    rewrite ?apply_beta1_comm.
    rewrite ?up_liftSub.
    rewrite ?ap_liftSub.
    econstructor; eauto with ws.
Qed.
Hint Resolve red_ren : ws.

Lemma redstar_ren {Γ γs τ1 τ2 k} (wγ: ⟨ Γ ⊢ γs : τ1 ↝* τ2 ∷ k ⟩) :
  ∀ Δ ζ, ⟨ ζ : Γ -> Δ ⟩ → ⟨ Δ ⊢ γs[ζ] : τ1[ζ] ↝* τ2[ζ] ∷ k ⟩.
Proof.
  induction wγ; intros ? ζ wζ; crush.
Qed.
Hint Resolve redstar_ren : ws.

Lemma tm_ren {Γ s τ} (wt: ⟨ Γ ⊢ s : τ ⟩) :
  ∀ Δ ζ, ⟨ ζ : Γ -> Δ ⟩ → ⟨ Δ ⊢ s[ζ] : τ[ζ] ⟩.
Proof.
  induction wt; intros ? ζ wζ; crush.
  - constructor; crush.
    rewrite <- ap_wkm_ix.
    rewrite apply_wkm_comm.
    rewrite ap_wkm_ix.
    apply IHwt; crush.
  - constructor; crush.
    rewrite <- ap_wkm_ix.
    rewrite apply_wkm_comm.
    rewrite ap_wkm_ix.
    apply IHwt; crush.
  - rewrite <- ?ap_liftSub.
    rewrite apply_beta1_comm.
    rewrite up_liftSub.
    rewrite ?ap_liftSub.
    crush.
  - econstructor; crush.
Qed.
Hint Resolve tm_ren : ws.

(*************************************************************************)

Lemma wtSub_closed ζ Δ : ⟨ ζ : nil => Δ ⟩.
Proof. constructor; inversion 1. Qed.
Hint Resolve wtSub_closed : ws.

Lemma wtSub_idm (Γ: Env) : ⟨ idm Exp : Γ => Γ ⟩.
Proof. constructor; crush. Qed.
Hint Resolve wtSub_idm : ws.

Lemma wtSub_wkm_tyvar Γ k :
  ⟨ wkm Exp : Γ => Γ ► k ⟩.
Proof. constructor; crush. Qed.
Hint Resolve wtSub_wkm_tyvar : ws.

Lemma wtSub_wkm_covar Γ τ1 τ2 k :
  ⟨ wkm Exp : Γ => Γ ◅ τ1 ~ τ2 ∷ k ⟩.
Proof. constructor; crush. Qed.
Hint Resolve wtSub_wkm_covar : ws.

Lemma wtSub_wkm_tmvar Γ τ :
  ⟨ wkm Exp : Γ => Γ ▻ τ ⟩.
Proof. constructor; crush. Qed.
Hint Resolve wtSub_wkm_tmvar : ws.

Lemma wtSub_snoc_tyvar {Γ Δ ζ τ k} :
  ⟨ ζ : Γ => Δ ⟩ →
  ⟨ Δ ⊢ τ ∷ k ⟩ →
  ⟨ ζ · τ : Γ ► k => Δ ⟩.
Proof.
  intros wζ wx; constructor; crush; repeat crushTypingMatchH;
    rewrite ?ap_comp, ?wkm_snoc_cancel; crush.
Qed.
Hint Resolve wtSub_snoc_tyvar : ws.

Lemma wtSub_snoc_covar {Γ Δ ζ γ τ1 τ2 k} :
  ⟨ ζ : Γ => Δ ⟩ →
  ⟨ Δ ⊢ γ : τ1[ζ] ~ τ2[ζ] ∷ k ⟩ →
  ⟨ ζ · γ : Γ ◅ τ1 ~ τ2 ∷ k => Δ ⟩.
Proof.
  intros wζ wx; constructor; crush; repeat crushTypingMatchH;
    rewrite ?ap_comp, ?wkm_snoc_cancel; crush.
Qed.
Hint Resolve wtSub_snoc_covar : ws.

Lemma wtSub_snoc_tmvar {Γ Δ ζ s τ} :
  ⟨ ζ : Γ => Δ ⟩ →
  ⟨ Δ ⊢ s : τ[ζ] ⟩ →
  ⟨ ζ · s : Γ ▻ τ => Δ ⟩.
Proof.
  intros wζ wx; constructor; crush; repeat crushTypingMatchH;
    rewrite ?ap_comp, ?wkm_snoc_cancel; crush.
Qed.
Hint Resolve wtSub_snoc_tmvar : ws.

Lemma wtSub_up_tyvar {Γ₁ Γ₂ ζ} (wζ: ⟨ ζ : Γ₁ => Γ₂ ⟩) :
  ∀ k, ⟨ ζ↑ : Γ₁ ► k => Γ₂ ► k ⟩.
Proof.
  rewrite up_def.
  constructor; crush.
  - inversion H; clear H; crush.
    rewrite <- ap_wkm_ix; crush.
  - inversion H; clear H; crush.
    rewrite ?ap_comp.
    rewrite ?wkm_snoc_cancel.
    rewrite <- ?ap_comp.
    rewrite <- ?(ap_wkm_ix (X:=Exp)).
    crush.
  - inversion H; clear H; crush.
    rewrite ?ap_comp.
    rewrite ?wkm_snoc_cancel.
    rewrite <- ?ap_comp.
    rewrite <- ?(ap_wkm_ix (X:=Exp)).
    crush.
Qed.
Hint Resolve wtSub_up_tyvar : ws.

Lemma wtSub_up_covar {Γ₁ Γ₂ ζ} (wζ: ⟨ ζ : Γ₁ => Γ₂ ⟩) :
  ∀ τ1 τ2 k, ⟨ ζ↑ : Γ₁ ◅ τ1 ~ τ2 ∷ k => Γ₂ ◅ τ1[ζ] ~ τ2[ζ] ∷ k ⟩.
Proof.
  rewrite up_def.
  constructor; crush.
  - inversion H; clear H; crush.
    rewrite <- ap_wkm_ix; crush.
  - inversion H; clear H; crush.
    + constructor.
      rewrite ?ap_comp.
      rewrite ?wkm_snoc_cancel.
      rewrite <- ?ap_comp.
      constructor.
    + rewrite ?ap_comp.
      rewrite ?wkm_snoc_cancel.
      rewrite <- ?ap_comp.
      rewrite <- ?(ap_wkm_ix (X:=Exp)).
      crush.
  - inversion H; clear H; crush.
    rewrite ?ap_comp.
    rewrite ?wkm_snoc_cancel.
    rewrite <- ?ap_comp.
    rewrite <- ?(ap_wkm_ix (X:=Exp)).
    crush.
Qed.
Hint Resolve wtSub_up_covar : ws.

Lemma wtSub_up_tmvar {Γ₁ Γ₂ ζ} (wζ: ⟨ ζ : Γ₁ => Γ₂ ⟩) :
  ∀ τ, ⟨ ζ↑ : Γ₁ ▻ τ => Γ₂ ▻ τ[ζ] ⟩.
Proof.
  rewrite up_def.
  constructor; crush.
  - inversion H; clear H; crush.
    rewrite <- ?(ap_wkm_ix (X:=Exp)).
    crush.
  - inversion H; clear H; crush.
    rewrite ?ap_comp.
    rewrite ?wkm_snoc_cancel.
    rewrite <- ?ap_comp.
    rewrite <- ?(ap_wkm_ix (X:=Exp)).
    crush.
  - inversion H; clear H; crush.
    + rewrite ap_comp.
      rewrite wkm_snoc_cancel.
      rewrite <- ap_comp.
      repeat constructor.
    + rewrite ap_comp.
      rewrite wkm_snoc_cancel.
      rewrite <- ap_comp.
      rewrite <- ?(ap_wkm_ix (X:=Exp)).
      crush.
Qed.
Hint Resolve wtSub_up_tmvar : ws.

Lemma ty_sub {Γ τ k} (wτ: ⟨ Γ ⊢ τ ∷ k ⟩) :
  ∀ Δ ζ, ⟨ ζ : Γ => Δ ⟩ → ⟨ Δ ⊢ τ[ζ] ∷ k ⟩.
Proof. induction wτ; crush. Qed.
Hint Resolve ty_sub : ws.

Lemma co_sub {Γ γ τ1 τ2 k} (wγ: ⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ k ⟩) :
  ∀ Δ ζ, ⟨ ζ : Γ => Δ ⟩ → ⟨ Δ ⊢ γ[ζ] : τ1[ζ] ~ τ2[ζ] ∷ k ⟩.
Proof. induction wγ; crush. Qed.
Hint Resolve co_sub : ws.

Lemma tm_sub {Γ s τ} (wt: ⟨ Γ ⊢ s : τ ⟩) :
  ∀ Δ ζ, ⟨ ζ : Γ => Δ ⟩ → ⟨ Δ ⊢ s[ζ] : τ[ζ] ⟩.
Proof.
  induction wt; intros ? ζ wζ; crush.
  - constructor; crush.
  - constructor; crush.
  - econstructor; crush.
Qed.
Hint Resolve tm_sub : ws.
