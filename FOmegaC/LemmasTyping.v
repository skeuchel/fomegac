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
    | [ H: ⟨ 0 : _ ∈ _ ⟩         |- _ ] =>
      inversion H; clear H; subst*
    | [ H: ⟨ (S _) : _ ∈ _ ⟩ |- _ ] =>
      inversion H; clear H; subst*
    | [ H: ⟨ 0 ∷ _ ∈ _ ⟩         |- _ ] =>
      inversion H; clear H; subst*
    | [ H: ⟨ (S _) ∷ _ ∈ _ ⟩ |- _ ] =>
      inversion H; clear H; subst*
    | [ H: ⟨ 0 : _ ~ _ ∷ _ ∈ _ ⟩         |- _ ] =>
      inversion H; clear H; subst*
    | [ H: ⟨ (S _) : _ ~ _ ∷ _ ∈ _ ⟩ |- _ ] =>
      inversion H; clear H; subst*
    (* | H: ⟪ _ ⊢ var _        : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ abs _ _      : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ app _ _      : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ unit         : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ true         : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ false        : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ ite _ _ _    : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ pair _ _     : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ proj₁ _      : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ proj₂ _      : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ inl _        : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ inr _        : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ caseof _ _ _ : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ seq _ _      : _ ⟫ |- _ => inversion H; clear H *)
    (* | H: ⟪ _ ⊢ fixt _ _ _   : _ ⟫ |- _ => inversion H; clear H *)
    (* | [ wi : ⟪ ?i : _ ∈ (_ ▻ _) ⟫ *)
    (*     |- context [match ?i with _ => _ end] *)
    (*   ] => destruct i *)
    | [ wi : ⟨ ?i : _ ∈ (_ ▻ _) ⟩ |- context [(_ · _) ?i] ] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i ∷ _ ∈ (_ ▻ _) ⟩ |- context [(_ · _) ?i] ] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i : _ ~ _ ∷ _ ∈ (_ ▻ _) ⟩ |- context [(_ · _) ?i] ] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i : _ ∈ (_ ► _) ⟩ |- context [(_ · _) ?i] ] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i ∷ _ ∈ (_ ► _) ⟩ |- context [(_ · _) ?i] ] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i : _ ~ _ ∷ _ ∈ (_ ► _) ⟩ |- context [(_ · _) ?i] ] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i : _ ∈ (_ ◅ _ ~ _ ∷ _) ⟩ |- context [(_ · _) ?i] ] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i ∷ _ ∈ (_ ◅ _ ~ _ ∷ _) ⟩ |- context [(_ · _) ?i] ] => destruct i eqn: ?; cbn in *
    | [ wi : ⟨ ?i : _ ~ _ ∷ _ ∈ (_ ◅ _ ~ _ ∷ _) ⟩ |- context [(_ · _) ?i] ] => destruct i eqn: ?; cbn in *
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
     (* repeat crushStlcSyntaxMatchH; *)
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasRewriteH;
     repeat crushSyntaxRefold;
     (* repeat crushTypingMatchH; *)
     subst*;
     try discriminate;
     eauto 200 with core ws;
     idtac
    ).

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

Lemma tm_ren {Γ s τ} (wt: ⟨ Γ ⊢ s : τ ⟩) :
  ∀ Δ ζ, ⟨ ζ : Γ -> Δ ⟩ → ⟨ Δ ⊢ s[ζ] : τ[ζ] ⟩.
Proof.
  induction wt; intros ? ζ wζ; crush.
  - constructor; crush.
    rewrite <- ap_wkm_ix.
    rewrite apply_wkm_comm.
    rewrite ap_wkm_ix.
    apply IHwt; crush.
  - constructor.
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


Record WtCoSub (Γ Δ: Env) (ζγ ζγi ζ1 ζ2: Sub Exp) : Prop :=
  { wcs_tyvar : ∀ {α k},
                  ⟨ α ∷ k ∈ Γ ⟩ →
                  ⟨ Δ ⊢ ζγ α : ζ1 α ~ ζ2 α ∷ k ⟩;
    wcs_covar : ∀ {c τ1 τ2 k},
                  ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ →
                  ⟨ Δ ⊢ ζγ c : τ1[ζ1] ~ τ2[ζ2] ∷ k ⟩;
    wcs_tyvari : ∀ {α k},
                  ⟨ α ∷ k ∈ Γ ⟩ →
                  ⟨ Δ ⊢ ζγi α : ζ2 α ~ ζ1 α ∷ k ⟩;
    wcs_covari : ∀ {c τ1 τ2 k},
                  ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ →
                  ⟨ Δ ⊢ ζγi c : τ1[ζ2] ~ τ2[ζ1] ∷ k ⟩;
    wtsub_left :> ⟨ ζ1 : Γ => Δ ⟩;
    wtsub_right :> ⟨ ζ2 : Γ => Δ ⟩;
  }.

Hint Resolve wcs_tyvar : ws.
Hint Resolve wcs_covar : ws.
Hint Resolve wcs_tyvari : ws.
Hint Resolve wcs_covari : ws.
Hint Resolve wtsub_left : ws.
Hint Resolve wtsub_right : ws.

(* Lemma wtSub_wkm_tyvar Γ k : *)
(*   ⟨ wkm Exp : Γ => Γ ► k ⟩. *)
(* Proof. constructor; crush. Qed. *)
(* Hint Resolve wtSub_wkm_tyvar : ws. *)

(* Lemma wtSub_wkm_covar Γ τ1 τ2 k : *)
(*   ⟨ wkm Exp : Γ => Γ ◅ τ1 ~ τ2 ∷ k ⟩. *)
(* Proof. constructor; crush. Qed. *)
(* Hint Resolve wtSub_wkm_covar : ws. *)

Definition upCoSub (ζγ: Sub Exp) : Sub Exp :=
  ((ζγ >=> wkm Exp) · corefl (var 0)).

Lemma wtCoSub_up_tyvar {Γ Δ ζγ ζγi ζ1 ζ2} (wζ: WtCoSub Γ Δ ζγ ζγi ζ1 ζ2) :
  ∀ k, WtCoSub (Γ ► k) (Δ ► k) (upCoSub ζγ) (upCoSub ζγi) ζ1↑ ζ2↑.
Proof.
  rewrite ?up_def.
  constructor; intros.
  - inversion H; clear H; crush.
  - inversion H; clear H; crush.
    rewrite ?ap_comp.
    rewrite ?wkm_snoc_cancel.
    rewrite <- ?ap_comp.
    rewrite <- ?(ap_wkm_ix (X:=Exp)).
    crush.
  - inversion H; clear H; crush.
  - inversion H; clear H; crush.
    rewrite ?ap_comp.
    rewrite ?wkm_snoc_cancel.
    rewrite <- ?ap_comp.
    rewrite <- ?(ap_wkm_ix (X:=Exp)).
    crush.
  - rewrite <- ?up_def; crush.
  - rewrite <- ?up_def; crush.
Qed.
Hint Resolve wtCoSub_up_tyvar : ws.

Fixpoint apCoSub (ζγ ζγi ζ1 ζ2: Sub Exp) (τ: Exp) {struct τ} : Exp :=
  match τ with
    | var α              =>  ζγ α
    | τabs k τ           =>  coτabs k (apCoSub (upCoSub ζγ) (upCoSub ζγi) ζ1↑ ζ2↑ τ)
    | τapp τ1 τ2         =>  coτapp (apCoSub ζγ ζγi ζ1 ζ2 τ1) (apCoSub ζγ ζγi ζ1 ζ2 τ2)
    | arr  τ1 τ2         =>  coarr  (apCoSub ζγ ζγi ζ1 ζ2 τ1) (apCoSub ζγ ζγi ζ1 ζ2 τ2)
    | arrτ k τ           =>  coarrτ k (apCoSub (upCoSub ζγ) (upCoSub ζγi) ζ1↑ ζ2↑ τ)
    | arrγ τ1 τ2 k τ3    =>  coarrγ (apCoSub ζγ ζγi ζ1 ζ2 τ1) (apCoSub ζγ ζγi ζ1 ζ2 τ2) k (apCoSub ζγ ζγi ζ1 ζ2 τ3)
    | coτabs k γ         =>  coτabs k (apCoSub (upCoSub ζγ) (upCoSub ζγi) ζ1↑ ζ2↑ γ)
    | coτapp γ1 γ2       =>  coτapp (apCoSub ζγ ζγi ζ1 ζ2 γ1) (apCoSub ζγ ζγi ζ1 ζ2 γ2)
    | coarr  γ1 γ2       =>  coarr  (apCoSub ζγ ζγi ζ1 ζ2 γ1) (apCoSub ζγ ζγi ζ1 ζ2 γ2)
    | coarrτ k γ         =>  coarrτ k (apCoSub (upCoSub ζγ) (upCoSub ζγi) ζ1↑ ζ2↑ γ)
    | coarrγ γ1 γ2 k γ3  =>  coarrγ (apCoSub ζγ ζγi ζ1 ζ2 γ1) (apCoSub ζγ ζγi ζ1 ζ2 γ2) k (apCoSub ζγ ζγi ζ1 ζ2 γ3)
    | coinvarr₁ γ        =>  coinvarr₁ (apCoSub ζγ ζγi ζ1 ζ2 γ)
    | coinvarr₂ γ        =>  coinvarr₂ (apCoSub ζγ ζγi ζ1 ζ2 γ)
    | coinvarrτ γ1 γ2    =>  coinvarrτ (apCoSub ζγ ζγi ζ1 ζ2 γ1) (apCoSub ζγ ζγi ζ1 ζ2 γ2)
    | coinvarrγ₁ γ       =>  coinvarrγ₁ (apCoSub ζγ ζγi ζ1 ζ2 γ)
    | coinvarrγ₂ γ       =>  coinvarrγ₂ (apCoSub ζγ ζγi ζ1 ζ2 γ)
    | coinvarrγ₃ γ       =>  coinvarrγ₃ (apCoSub ζγ ζγi ζ1 ζ2 γ)
    | cobeta γ1 γ2       =>  cobeta (apCoSub (upCoSub ζγ) (upCoSub ζγi) ζ1↑ ζ2↑ γ1) (apCoSub ζγ ζγi ζ1 ζ2 γ2)
    | corefl τ           =>  apCoSub ζγ ζγi ζ1 ζ2 τ
    | cosym γ            =>  cosym (apCoSubSym ζγ ζγi ζ1 ζ2 γ)
    | cotrans γ1 γ2      =>  cotrans (apCoSub ζγ ζγi ζ1 ζ2 γ1) γ2[ζ2]
    | _ => var 0
  end
with apCoSubSym (ζγ ζγi ζ1 ζ2: Sub Exp) (τ: Exp) {struct τ} : Exp :=
  match τ with
    | var α              =>  ζγi α
    | τabs k τ           =>  coτabs k (apCoSubSym (upCoSub ζγ) (upCoSub ζγi) ζ1↑ ζ2↑ τ)
    | τapp τ1 τ2         =>  coτapp (apCoSubSym ζγ ζγi ζ1 ζ2 τ1) (apCoSubSym ζγ ζγi ζ1 ζ2 τ2)
    | arr  τ1 τ2         =>  coarr  (apCoSubSym ζγ ζγi ζ1 ζ2 τ1) (apCoSubSym ζγ ζγi ζ1 ζ2 τ2)
    | arrτ k τ           =>  coarrτ k (apCoSubSym (upCoSub ζγ) (upCoSub ζγi) ζ1↑ ζ2↑ τ)
    | arrγ τ1 τ2 k τ3    =>  coarrγ (apCoSubSym ζγ ζγi ζ1 ζ2 τ1) (apCoSubSym ζγ ζγi ζ1 ζ2 τ2) k (apCoSubSym ζγ ζγi ζ1 ζ2 τ3)
    | coτabs k γ         =>  coτabs k (apCoSubSym (upCoSub ζγ) (upCoSub ζγi) ζ1↑ ζ2↑ γ)
    | coτapp γ1 γ2       =>  coτapp (apCoSubSym ζγ ζγi ζ1 ζ2 γ1) (apCoSubSym ζγ ζγi ζ1 ζ2 γ2)
    | coarr  γ1 γ2       =>  coarr  (apCoSubSym ζγ ζγi ζ1 ζ2 γ1) (apCoSubSym ζγ ζγi ζ1 ζ2 γ2)
    | coarrτ k γ         =>  coarrτ k (apCoSubSym (upCoSub ζγ) (upCoSub ζγi) ζ1↑ ζ2↑ γ)
    | coarrγ γ1 γ2 k γ3  =>  coarrγ (apCoSubSym ζγ ζγi ζ1 ζ2 γ1) (apCoSubSym ζγ ζγi ζ1 ζ2 γ2) k (apCoSubSym ζγ ζγi ζ1 ζ2 γ3)
    | coinvarr₁ γ        =>  coinvarr₁ (apCoSubSym ζγ ζγi ζ1 ζ2 γ)
    | coinvarr₂ γ        =>  coinvarr₂ (apCoSubSym ζγ ζγi ζ1 ζ2 γ)
    | coinvarrτ γ1 γ2    =>  coinvarrτ (apCoSubSym ζγ ζγi ζ1 ζ2 γ1) (apCoSubSym ζγ ζγi ζ1 ζ2 γ2)
    | coinvarrγ₁ γ       =>  coinvarrγ₁ (apCoSubSym ζγ ζγi ζ1 ζ2 γ)
    | coinvarrγ₂ γ       =>  coinvarrγ₂ (apCoSubSym ζγ ζγi ζ1 ζ2 γ)
    | coinvarrγ₃ γ       =>  coinvarrγ₃ (apCoSubSym ζγ ζγi ζ1 ζ2 γ)
    | cobeta γ1 γ2       =>  cobeta (apCoSubSym (upCoSub ζγ) (upCoSub ζγi) ζ1↑ ζ2↑ γ1) (apCoSubSym ζγ ζγi ζ1 ζ2 γ2)
    | corefl τ           =>  apCoSubSym ζγ ζγi ζ1 ζ2 τ
    | cosym γ            =>  cosym (apCoSub ζγ ζγi ζ1 ζ2 γ)
    | cotrans γ1 γ2      =>  cotrans γ1[ζ2] (apCoSubSym ζγ ζγi ζ1 ζ2 γ2)
    | _ => var 0
  end.

Lemma ty_cosub {Γ τ k} (wτ: ⟨ Γ ⊢ τ ∷ k ⟩) :
  ∀ Δ ζγ ζγi ζ1 ζ2,
    WtCoSub Γ Δ ζγ ζγi ζ1 ζ2 →
    ⟨ Δ ⊢ apCoSub ζγ ζγi ζ1 ζ2 τ : τ[ζ1] ~ τ[ζ2] ∷ k ⟩
with ty_cosubsym {Γ τ k} (wτ: ⟨ Γ ⊢ τ ∷ k ⟩) :
  ∀ Δ ζγ ζγi ζ1 ζ2,
    WtCoSub Γ Δ ζγ ζγi ζ1 ζ2 →
    ⟨ Δ ⊢ apCoSubSym ζγ ζγi ζ1 ζ2 τ : τ[ζ2] ~ τ[ζ1] ∷ k ⟩.
Proof.
  - induction wτ; crush.
  - induction wτ; crush.
Qed.
Hint Resolve ty_cosub : ws.
Hint Resolve ty_cosubsym : ws.

Lemma co_cosub {Γ γ τ1 τ2 k} (wγ: ⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ k ⟩) :
  ∀ Δ ζγ ζγi ζ1 ζ2,
    WtCoSub Γ Δ ζγ ζγi ζ1 ζ2 →
    ⟨ Δ ⊢ apCoSub ζγ ζγi ζ1 ζ2 γ : τ1[ζ1] ~ τ2[ζ2] ∷ k ⟩
with co_cosubsym {Γ γ τ1 τ2 k} (wγ: ⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ k ⟩) :
  ∀ Δ ζγ ζγi ζ1 ζ2,
    WtCoSub Γ Δ ζγ ζγi ζ1 ζ2 →
    ⟨ Δ ⊢ apCoSubSym ζγ ζγi ζ1 ζ2 γ : τ1[ζ2] ~ τ2[ζ1] ∷ k ⟩.
Proof.
  - induction wγ; crush.
  - induction wγ; crush.
Qed.
Hint Resolve co_cosub : ws.
Hint Resolve co_cosubsym : ws.
