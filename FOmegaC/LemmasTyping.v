Require Export ParDB.Spec.
Require Export ParDB.Lemmas.
Require Export ParDB.Inst.

Require Export SpecSyntax.
Require Export SpecTyping.

Require  Coq.Setoids.Setoid.

Record WtRen (Γ Δ: Env) (ζ: Sub Ix) : Prop :=
  { wtr_evar : ∀ {x τ},
                 ⟨ x : τ ∈ Γ ⟩ →
                 ⟨ ζ x : τ[ζ] ∈ Δ ⟩;
    wtr_tvar : ∀ {α k},
                 ⟨ α ∷ k ∈ Γ ⟩ →
                 ⟨ ζ α ∷ k ∈ Δ ⟩;
    wtr_cvar : ∀ {c τ1 τ2 k},
                 ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ →
                 ⟨ ζ c : τ1[ζ] ~ τ2[ζ] ∷ k ∈ Δ ⟩
  }.
Notation "⟨ ζ : Γ -> Δ ⟩" := (WtRen Γ Δ ζ)
  (at level 0,
   ζ at level 98,
   Γ at level 98,
   Δ at level 98).

Arguments wtr_evar {_ _ _} _ {_ _} _.
Arguments wtr_tvar {_ _ _} _ {_ _} _.
Arguments wtr_cvar {_ _ _} _ {_ _ _ _} _.

Record WtSub (Γ Δ: Env) (ζ: Sub Tm) : Prop :=
  { wts_evar : ∀ {x τ},
                 ⟨ x : τ ∈ Γ ⟩ →
                 ⟨ Δ ⊢ ζ x : τ[ζ] ⟩;
    wts_tvar : ∀ {α k},
                 ⟨ α ∷ k ∈ Γ ⟩ →
                 ⟨ Δ ⊢ ζ α ∷ k ⟩;
    wts_cvar : ∀ {c τ1 τ2 k},
                 ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ →
                 ⟨ Δ ⊢ ζ c : τ1[ζ] ~ τ2[ζ] ∷ k ⟩
  }.
Notation "⟨ ζ : Γ => Δ ⟩" := (WtSub Γ Δ ζ).
  (* (at level 0, *)
  (*  ζ at level 98, *)
  (*  Γ at level 98, *)
  (*  Δ at level 98). *)

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

Hint Constructors GetEVar : ws.
Hint Constructors GetTVar : ws.
Hint Constructors GetCVar : ws.

Local Ltac crush :=
  intros; cbn in * |-;
  repeat
    (cbn;
     (* repeat crushStlcSyntaxMatchH; *)
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasRewriteH;
     (* repeat crushTypingMatchH; *)
     subst*;
     idtac);
  try discriminate;
  eauto with core ws.

Section Renaming.

  (* Lemma getEvar_wsIx Γ i T : *)
  (*   ⟪ i : T ∈ Γ ⟫ → dom Γ ∋ i. *)
  (* Proof. induction 1; crush. Qed. *)
  (* Hint Resolve getEvar_wsIx : ws. *)

  (* Lemma wsIx_getEvar {Γ i} (wi: dom Γ ∋ i) : *)
  (*   ∀ (P: Prop), (∀ T, ⟪ i : T ∈ Γ ⟫ → P) → P. *)
  (* Proof. *)
  (*   depind wi; destruct Γ; crush. *)
  (*   - eapply (IHwi _ x); crush. *)
  (* Qed. *)

  (* Lemma wtRen_wsRen Γ₁ Γ₂ ξ : *)
  (*   WtRen Γ₁ Γ₂ ξ → WsRen (dom Γ₁) (dom Γ₂) ξ. *)
  (* Proof. *)
  (*   unfold WtRen, WsRen; intros. *)
  (*   apply (wsIx_getEvar H0); crush. *)
  (* Qed. *)

  (* Lemma typing_wt {Γ t T} (wt: ⟪ Γ ⊢ t : T ⟫) : *)
  (*   wsTm (dom Γ) t. *)
  (* Proof. induction wt; crush. Qed. *)

  (* Lemma wtSub_wsSub Γ₁ Γ₂ ζ : *)
  (*   WtSub Γ₁ Γ₂ ζ → WsSub (dom Γ₁) (dom Γ₂) ζ. *)
  (* Proof. *)
  (*   unfold WtSub, WsSub; intros. *)
  (*   apply (wsIx_getEvar H0); crush. *)
  (*   eauto using typing_wt. *)
  (* Qed. *)

  (*************************************************************************)

  Lemma wtRen_closed {ζ Δ} :
    ⟨ ζ : nil -> Δ ⟩.
  Proof.
    constructor; inversion 1.
  Qed.
  Hint Resolve wtRen_closed : ws.

  Lemma wtRen_idm Γ :
    ⟨ idm Ix : Γ -> Γ ⟩.
  Proof.
    constructor; crush.
  Qed.
  Hint Resolve wtRen_idm : ws.

  Lemma wtRen_comp {Γ₁ Γ₂ Γ₃ ξ₁ ξ₂} :
    ⟨ ξ₁ : Γ₁ -> Γ₂ ⟩ →
    ⟨ ξ₂ : Γ₂ -> Γ₃ ⟩ →
    ⟨ ξ₁ >=> ξ₂ : Γ₁ -> Γ₃ ⟩.
  Proof.
    do 2 inversion 1.
    constructor; crush.
  Qed.
  Hint Resolve wtRen_comp : ws.

  (*************************************************************************)

  (* Definition WtRenNatural (Γ₁ Γ₂: Env) (ξ₁ ξ₂: Sub Ix) : Prop := *)
  (*   ∀ i T, ⟪ (ξ₁ i) : T ∈ Γ₁ ⟫ → ⟪ (ξ₂ i) : T ∈ Γ₂ ⟫. *)

  (* Lemma wtRen_natural *)
  (*   {f₁ f₂: Env → Env} {ξ₁ ξ₂: Sub Ix} *)
  (*   (hyp: ∀ Γ, WtRenNatural (f₁ Γ) (f₂ Γ) ξ₁ ξ₂) : *)
  (*   ∀ Γ₁ Γ₂ ξ, *)
  (*     WtRen Γ₁ (f₁ Γ₂) (ξ >-> ξ₁) → *)
  (*     WtRen Γ₁ (f₂ Γ₂) (ξ >-> ξ₂). *)
  (* Proof. unfold WtRenNatural, WtRen in *; eauto. Qed. *)

  (*************************************************************************)

  (* Lemma wtRen_wkms (Δ: Env) : *)
  (*   ∀ Γ, WtRen Γ (Γ ▻▻ Δ) (wkms (dom Δ)). *)
  (* Proof. unfold WtRen. induction Δ; crush. Qed. *)
  (* Hint Resolve wtRen_wkms : ws. *)

  (* Lemma wtiIx_wkms (Δ: Env) : *)
  (*   ∀ (Γ: Env) (i: Ix) T, *)
  (*     ⟪ (wkms (dom Δ) i) : T ∈ (Γ ▻▻ Δ) ⟫ → ⟪ i : T ∈ Γ ⟫. *)
  (* Proof. induction Δ; eauto with wsi. Qed. *)
  (* Hint Resolve wtiIx_wkms : wsi. *)


  Lemma wtRen_wkm_evar Γ τ :
    ⟨ wkm : Γ -> Γ ▻ τ ⟩.
  Proof.
    constructor; intros;
    rewrite <- ?ap_liftSub;
    crush.
  Qed.
  Hint Resolve wtRen_wkm_evar : ws.

  Lemma wtRen_wkm_tvar Γ k :
    ⟨ wkm : Γ -> Γ ► k ⟩.
  Proof.
    constructor; intros;
    rewrite <- ?ap_liftSub;
    crush.
  Qed.
  Hint Resolve wtRen_wkm_tvar : ws.

  Lemma wtRen_wkm_cvar Γ τ1 τ2 k :
    ⟨ wkm : Γ -> Γ ◅ τ1 ~ τ2 ∷ k ⟩.
  Proof.
    constructor; intros;
    rewrite <- ?ap_liftSub;
    crush.
  Qed.
  Hint Resolve wtRen_wkm_cvar : ws.

  (* Lemma wtiIx_wkm Γ i T : *)
  (*   ⟪ (wkm i) : T ∈ (Γ ▻ T) ⟫ → ⟪ i : T ∈ Γ ⟫. *)
  (* Proof. apply (wtiIx_wkms (empty ▻ T)). Qed. *)
  (* Hint Resolve wtiIx_wkm : wsi. *)

  (* Lemma wtRenNatural_wkms_id Δ : *)
  (*   ∀ Γ, WtRenNatural (Γ ▻▻ Δ) Γ (wkms (dom Δ)) (idm Ix). *)
  (* Proof. unfold WtRenNatural; eauto using wtiIx_wkms. Qed. *)
  (* Hint Resolve wtRenNatural_wkms_id : wsi. *)

  (* Lemma wtiRen_comp_wkms Δ : *)
  (*   ∀ Γ₁ Γ₂ ξ, *)
  (*     WtRen Γ₁ (Γ₂ ▻▻ Δ) (ξ >-> wkms (dom Δ)) → *)
  (*     WtRen Γ₁ Γ₂        ξ. *)
  (* Proof. apply (wtRen_natural (wtRenNatural_wkms_id Δ)). Qed. *)
  (* Hint Resolve wtiRen_comp_wkms : wsi. *)

  Lemma wtRen_snoc_evar {Γ Δ ζ x τ} :
    ⟨ ζ : Γ -> Δ ⟩ →
    ⟨ x : τ[ζ] ∈ Δ ⟩ →
    ⟨ ζ · x : Γ ▻ τ -> Δ ⟩.
  Proof.
    intros wζ wx; constructor; crush.
    - repeat crushTypingMatchH; crush.
      + rewrite <- ap_liftSub.
        rewrite liftSub_snoc.
        rewrite ap_comp.
        rewrite wkm_snoc_cancel.
        rewrite ap_liftSub.
        assumption.
      + rewrite <- ap_liftSub.
        rewrite liftSub_snoc.
        rewrite ap_comp.
        rewrite wkm_snoc_cancel.
        rewrite ap_liftSub.
        now apply (wtr_evar wζ).
    - repeat crushTypingMatchH; crush.
      now apply (wtr_tvar wζ).
    - repeat crushTypingMatchH; crush.
      rewrite <- ?ap_liftSub.
      rewrite ?liftSub_snoc.
      rewrite ?ap_comp.
      rewrite ?wkm_snoc_cancel.
      rewrite ?ap_liftSub.
      now apply (wtr_cvar wζ).
  Qed.
  Hint Resolve wtRen_snoc_evar : ws.

  Lemma wtRen_snoc_tvar {Γ Δ ζ α k} :
    ⟨ ζ : Γ -> Δ ⟩ →
    ⟨ α ∷ k ∈ Δ ⟩ →
    ⟨ ζ · α : Γ ► k -> Δ ⟩.
  Proof.
    intros wζ wα; constructor; crush.
    - repeat crushTypingMatchH; crush.
      rewrite <- ap_liftSub.
      rewrite liftSub_snoc.
      rewrite ap_comp.
      rewrite wkm_snoc_cancel.
      rewrite ap_liftSub.
      now apply (wtr_evar wζ).
    - repeat crushTypingMatchH; crush.
      now apply (wtr_tvar wζ).
    - repeat crushTypingMatchH; crush.
      rewrite <- ?ap_liftSub.
      rewrite ?liftSub_snoc.
      rewrite ?ap_comp.
      rewrite ?wkm_snoc_cancel.
      rewrite ?ap_liftSub.
      now apply (wtr_cvar wζ).
  Qed.
  Hint Resolve wtRen_snoc_tvar : ws.

  Lemma wtRen_snoc_cvar {Γ Δ ζ c τ1 τ2 k} :
    ⟨ ζ : Γ -> Δ ⟩ →
    ⟨ c : τ1[ζ] ~ τ2[ζ] ∷ k ∈ Δ ⟩ →
    ⟨ ζ · c : Γ ◅ τ1 ~ τ2 ∷ k -> Δ ⟩.
  Proof.
    intros wζ wc; constructor; crush.
    - repeat crushTypingMatchH; crush.
      rewrite <- ap_liftSub.
      rewrite liftSub_snoc.
      rewrite ap_comp.
      rewrite wkm_snoc_cancel.
      rewrite ap_liftSub.
      now apply (wtr_evar wζ).
    - repeat crushTypingMatchH; crush.
      now apply (wtr_tvar wζ).
    - repeat crushTypingMatchH; crush.
      + rewrite <- ?ap_liftSub.
        rewrite ?liftSub_snoc.
        rewrite ?ap_comp.
        rewrite ?wkm_snoc_cancel.
        rewrite ?ap_liftSub.
        assumption.
      + rewrite <- ?ap_liftSub.
        rewrite ?liftSub_snoc.
        rewrite ?ap_comp.
        rewrite ?wkm_snoc_cancel.
        rewrite ?ap_liftSub.
        now apply (wtr_cvar wζ).
  Qed.
  Hint Resolve wtRen_snoc_cvar : ws.

  (* Lemma wtiRen_snoc Γ₁ Γ₂ T ξ x : *)
  (*   WtRen (Γ₁ ▻ T) Γ₂ (ξ · x) → WtRen Γ₁ Γ₂ ξ. *)
  (* Proof. *)
  (*   intros wξ i. specialize (wξ (S i)). eauto using GetEvar. *)
  (* Qed. *)
  (* Hint Resolve wtiRen_snoc : wsi. *)

  (* Lemma wtiIx_snoc Γ₁ Γ₂ ξ T x : *)
  (*   WtRen (Γ₁ ▻ T) Γ₂ (ξ · x) → ⟪ x : T ∈ Γ₂ ⟫. *)
  (* Proof. *)
  (*   intros wξ. specialize (wξ 0). eauto using GetEvar. *)
  (* Qed. *)
  (* Hint Resolve wtiIx_snoc : wsi. *)

  Lemma wtRen_up_evar {Γ₁ Γ₂ ζ} (wζ: ⟨ ζ : Γ₁ -> Γ₂ ⟩) :
    ∀ τ : Tm, ⟨ ζ↑ : Γ₁ ▻ τ -> Γ₂ ▻ τ[ζ] ⟩.
  Proof.
    rewrite up_def.
    constructor; crush.
    - inversion H; clear H; crush.
      + rewrite <- ?ap_liftSub.
        rewrite ?liftSub_snoc.
        rewrite ?ap_comp.
        rewrite ?wkm_snoc_cancel.
        rewrite liftSub_comp.
        rewrite liftSub_wkm.
        rewrite <- ?ap_comp.
        rewrite ?ap_liftSub.
        constructor.
      + (* rewrite <- ap_liftSub at 4. *)
        rewrite <- (ap_liftSub _ ((ζ >=> wkm) · 0)).
        rewrite ?liftSub_snoc.
        rewrite ?ap_comp.
        rewrite ?wkm_snoc_cancel.
        rewrite liftSub_comp.
        rewrite liftSub_wkm.
        rewrite <- ?ap_comp.
        rewrite ?ap_liftSub.
        constructor.
        now apply (wtr_evar wζ).
    - repeat crushTypingMatchH; crush.
      constructor.
      now apply (wtr_tvar wζ).
    - repeat crushTypingMatchH; crush.
      rewrite <- ?(ap_liftSub _ ((ζ >=> wkm) · 0)).
      rewrite ?liftSub_snoc.
      rewrite ?ap_comp.
      rewrite ?wkm_snoc_cancel.
      rewrite liftSub_comp.
      rewrite liftSub_wkm.
      rewrite <- ?ap_comp.
      rewrite ?ap_liftSub.
      econstructor.
      now apply (wtr_cvar wζ).
  Qed.
  Hint Resolve wtRen_up_evar : ws.

  (*
  Lemma wtiRen_up Γ₁ Γ₂ ξ T :
    WtRen (Γ₁ ▻ T) (Γ₂ ▻ T) (ξ ↑) → WtRen Γ₁ Γ₂ ξ.
  Proof.
    unfold up, WtRen. crush.
    specialize (H (S i) T0). eauto with ws wsi.
  Qed.
  Hint Resolve wtiRen_up : wsi.

  Lemma wtRen_ups Γ₁ Γ₂ Δ ξ :
    WtRen Γ₁ Γ₂ ξ → WtRen (Γ₁ ▻▻ Δ) (Γ₂ ▻▻ Δ) (ξ ↑⋆ dom Δ).
  Proof. induction Δ; crush. Qed.
  Hint Resolve wtRen_ups : ws.

  Lemma wtiRen_ups Γ₁ Γ₂ Δ ξ :
    WtRen (Γ₁ ▻▻ Δ) (Γ₂ ▻▻ Δ) (ξ ↑⋆ dom Δ) → WtRen Γ₁ Γ₂ ξ.
  Proof. induction Δ; eauto with wsi. Qed.
  Hint Resolve wtiRen_ups : wsi.

  Lemma wtRen_beta (Γ Δ: Env) :
    ∀ ξ, WtRen Δ Γ ξ → WtRen (Γ ▻▻ Δ) Γ (beta (dom Δ) ξ).
  Proof. unfold WtRen; induction Δ; crush. Qed.
  Hint Resolve wtRen_beta : ws.

  Lemma typing_ren {Γ₁ t T} (wt: ⟪ Γ₁ ⊢ t : T ⟫) :
    ∀ Γ₂ ξ, WtRen Γ₁ Γ₂ ξ → ⟪ Γ₂ ⊢ t[ξ] : T ⟫.
  Proof. induction wt; econstructor; crush. Qed.
  Hint Resolve typing_ren : ws.

End Renaming.

Section Substitution.

  (* Lemma typing_weakening Δ {Γ t T} (wt: ⟪ Γ ⊢ t : T ⟫) : *)
  (*   ⟪ Γ ▻▻ Δ ⊢ t[@wkms Ix _ _ (dom Δ)] : T ⟫. *)
  (* Proof. apply (typing_ren wt), wtRen_wkms. Qed. *)

  (* Lemma typing_weakening1 T' {Γ t T} (wt: ⟪ Γ ⊢ t : T ⟫) : *)
  (*   ⟪ Γ ▻ T' ⊢ t[@wkm Ix _ _] : T ⟫. *)
  (* Proof. apply (typing_weakening (empty ▻ T') wt). Qed. *)

  (*************************************************************************)

  Lemma wtSub_closed ζ Δ : WtSub empty Δ ζ.
  Proof. inversion 1. Qed.
  Hint Resolve wtSub_closed : ws.

  Lemma wtSub_idm (Γ: Env) : WtSub Γ Γ (idm Tm).
  Proof. unfold WtSub. crush. Qed.
  Hint Resolve wtSub_idm : ws.

  Lemma wtSub_snoc Γ₁ Γ₂ ζ t T :
    WtSub Γ₁ Γ₂ ζ → ⟪ Γ₂ ⊢ t : T ⟫ → WtSub (Γ₁ ▻ T) Γ₂ (ζ · t).
  Proof. unfold WtSub. crush. Qed.
  Hint Resolve wtSub_snoc : ws.

  Lemma wtiSub_snoc Γ₁ Γ₂ T ζ t :
    WtSub (Γ₁ ▻ T) Γ₂ (ζ · t) → WtSub Γ₁ Γ₂ ζ.
  Proof.
    intros wζ i. specialize (wζ (S i)). eauto using GetEvar.
  Qed.
  Hint Resolve wtiSub_snoc : wsi.

  Lemma wtSub_toSub ξ Γ₁ Γ₂ :
    WtRen Γ₁ Γ₂ ξ → WtSub Γ₁ Γ₂ ⌈ξ⌉.
  Proof. unfold WtRen, WtSub; eauto using WtVar. Qed.

  Lemma wtSub_wkms (Δ: Env) :
    ∀ Γ, WtSub Γ (Γ ▻▻ Δ) ⌈@wkms Ix _ _ (dom Δ)⌉.
  Proof. eauto using wtRen_wkms, wtSub_toSub. Qed.
  Hint Resolve wtSub_wkms : ws.

  Lemma wtSub_wkm Γ T :
    WtSub Γ (Γ ▻ T) ⌈wkm⌉.
  Proof. apply (wtSub_wkms (empty ▻ T)). Qed.
  Hint Resolve wtSub_wkm : ws.

  Lemma wtSub_up {Γ₁ Γ₂ ζ} (wζ: WtSub Γ₁ Γ₂ ζ) :
    ∀ T, WtSub (Γ₁ ▻ T) (Γ₂ ▻ T) (ζ ↑).
  Proof. inversion 1; crush. Qed.
  Hint Resolve wtSub_up : ws.

  Lemma wtSub_ups Γ₁ Γ₂ Δ ζ :
    WtSub Γ₁ Γ₂ ζ → WtSub (Γ₁ ▻▻ Δ) (Γ₂ ▻▻ Δ) (ζ ↑⋆ dom Δ).
  Proof. induction Δ; crush. Qed.
  Hint Resolve wtSub_ups : ws.

  Lemma typing_sub {Γ₁ t T} (wt: ⟪ Γ₁ ⊢ t : T ⟫) :
    ∀ Γ₂ ζ, WtSub Γ₁ Γ₂ ζ → ⟪ Γ₂ ⊢ t[ζ] : T ⟫.
  Proof. induction wt; crush. Qed.
  Hint Resolve typing_sub : ws.

  Lemma wtSub_comp {Γ₁ Γ₂ Γ₃ ζ₁ ζ₂} :
    WtSub Γ₁ Γ₂ ζ₁ → WtSub Γ₂ Γ₃ ζ₂ → WtSub Γ₁ Γ₃ (ζ₁ >=> ζ₂).
  Proof. unfold WtSub, comp; eauto with ws. Qed.
  Hint Resolve wtSub_comp : ws.

  Lemma wtiTm_snoc Γ₁ Γ₂ ζ T t :
    WtSub (Γ₁ ▻ T) Γ₂ (ζ · t) → ⟪ Γ₂ ⊢ t : T ⟫.
  Proof.
    intros wζ. specialize (wζ 0). eauto using GetEvar.
  Qed.
  Hint Resolve wtiTm_snoc : wsi.

  (*************************************************************************)

  Lemma wtSub_beta (Γ Δ: Env) :
    ∀ ζ, WtSub Δ Γ ζ → WtSub (Γ ▻▻ Δ) Γ (beta (dom Δ) ζ).
  Proof.
    unfold WtSub; induction Δ; crush.
  Qed.
  Hint Resolve wtSub_beta : ws.

  Lemma wtSub_beta1 Γ t T (wi: ⟪ Γ ⊢ t : T ⟫) :
    WtSub (Γ ▻ T) Γ (beta1 t).
  Proof. apply (wtSub_beta Γ (empty ▻ T)); crush. Qed.
  Hint Resolve wtSub_beta1 : ws.

  (*************************************************************************)

  (* Lemma typing_beta {Γ Δ t T ζ} : *)
  (*   WtSub Δ Γ ζ → ⟪ (Γ ▻▻ Δ) ⊢ t : T ⟫ → ⟪ Γ ⊢ t[beta (dom Δ) ζ] : T ⟫. *)
  (* Proof. intros; eapply typing_sub; eauto with ws. Qed. *)

  (* Lemma typing_beta1 {Γ t T t' T'} : *)
  (*   ⟪ Γ ⊢ t' : T' ⟫ → ⟪ Γ ▻ T' ⊢ t : T ⟫ → ⟪ Γ ⊢ t[beta1 t'] : T ⟫. *)
  (* Proof. intros; eapply typing_sub; eauto with ws. Qed. *)

  (*************************************************************************)

  Ltac crushTypingMatchH2 :=
    match goal with
      | [ |- ⟪ _ ⊢ @ap Tm Ix vrIx _ ?ξ ?t : _ ⟫
        ] => eapply typing_ren
      | [ |- ⟪ _ ⊢ @ap Tm Tm vrTm _ ?ζ ?t : _ ⟫
        ] => eapply typing_sub
      | [ |- WtSub (_ ▻ _) _ (beta _ _)
        ] => eapply wtSub_beta
      | [ |- WtSub (_ ▻ _) _ (beta1 _)
        ] => eapply wtSub_beta1
    end.

  Ltac crushTyping :=
    intros; cbn in * |-;
    repeat
    (cbn;
     repeat crushStlcSyntaxMatchH;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasMatchH;
     repeat crushTypingMatchH;
     repeat crushTypingMatchH2;
     eauto with ws
    ).

  Hint Extern 20 (⟪ _ ⊢ _ : _ ⟫) =>
  crushTyping : typing.

End Substitution.
*)