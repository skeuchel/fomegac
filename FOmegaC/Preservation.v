Require Import Coq.Lists.List.
Require Export ParDB.Spec.
Require Export ParDB.Lemmas.
Require Export ParDB.Inst.

Require Export SpecSyntax.
Require Export SpecTyping.
Require Export SpecEvaluation.
Require Export LemmasTyping.
Require Export Agreement.
Require Export Consistency.

Local Ltac crush :=
  intros;
  repeat
    (cbn in *;
     repeat crushIH;
     repeat crushSyntaxMatch;
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasRewriteH;
     repeat crushSyntaxRefold;
     repeat crushTypingMatchH;
     subst*;
     try discriminate;
     eauto with ws;
     destruct_conjs;
     idtac
    ).


(******************************************************************************)
(* Preservation                                                               *)
(******************************************************************************)

Lemma arr_inversion {Γ γ σ1 σ2 τ1 τ2} (wΓ: WfEnv Γ) (clΓ: CoVarClosed Γ)
  (wγ: ⟨ Γ ⊢ γ : arr σ1 σ2 ~ arr τ1 τ2 ∷ kstar ⟩) :
  (∃ γ1, ⟨ Γ ⊢ γ1 : σ1 ~ τ1 ∷ kstar ⟩) ∧
  (∃ γ2, ⟨ Γ ⊢ γ2 : σ2 ~ τ2 ∷ kstar ⟩).
Proof.
  apply co_red in wγ; auto.
  destruct wγ as (υ & (γs & wγs) & (ηs & wηs)).
  apply arr_consistency in wγs; auto.
  apply arr_consistency in wηs; auto.
  destruct wγs as (υ1 & υ2 & Heqυ & ((υγ1 & Hυ1) & (υγ2 & Hυ2))).
  destruct wηs as (υ1' & υ2' & Heqυ' & ((υγ1' & Hυ1') & (υγ2' & Hυ2'))).
  rewrite Heqυ in Heqυ'; inversion Heqυ'; subst υ1' υ2'; clear Heqυ Heqυ'.
  repeat
    match goal with
      | [H: ⟨ _ ⊢ _ : _ ↝* _ ∷ _ ⟩ |- _ ] =>
        eapply redstar_co in H
      | [H: ⟨ Γ ⊢ cofromredstar ?σ ?γs : _ ~ _ ∷ _ ⟩ |- _ ] =>
        generalize dependent (cofromredstar σ γs);
          clear γs; intros γs ?
    end.
  split.
  - eexists (cotrans υγ1' (cosym υγ1)); crush.
  - eexists (cotrans υγ2' (cosym υγ2)); crush.
Qed.

Lemma abs_inversion' {Γ t σ1 σ} (wΓ: WfEnv Γ) (clΓ: CoVarClosed Γ)
  (wt: ⟨ Γ ⊢ abs σ1 t : σ⟩) :
  ∀ γ τ1 τ2,
    ⟨ Γ ⊢ γ : σ ~ arr τ1 τ2 ∷ kstar ⟩ →
    (∃ γ1, ⟨ Γ ⊢ γ1 : τ1 ~ σ1 ∷ kstar ⟩) ∧
    (∃ γ2 σ2,
       ⟨ Γ ⊢ γ2 : σ2 ~ τ2 ∷ kstar ⟩ ∧
       ⟨ Γ ▻ σ1 ⊢ cast t γ2[wkm Exp] : τ2[wkm Exp] ⟩).
Proof.
  depind wt; intros γ τ1' τ2' wγ.
  apply arr_inversion in wγ; auto.
  destruct wγ as ((γ1 & wγ1) & (γ2 & wγ2)).
  split.
  - exists (cosym γ1); crush.
  - exists γ2, τ2; crush.
Qed.

Lemma abs_inversion {Γ t σ1 τ1 τ2} (wΓ: WfEnv Γ) (clΓ: CoVarClosed Γ)
  (wt: ⟨ Γ ⊢ abs σ1 t : arr τ1 τ2 ⟩) :
  (∃ γ1, ⟨ Γ ⊢ γ1 : τ1 ~ σ1 ∷ kstar ⟩) ∧
  (∃ γ2 σ2,
     ⟨ Γ ⊢ γ2 : σ2 ~ τ2 ∷ kstar ⟩ ∧
     ⟨ Γ ▻ σ1 ⊢ cast t γ2[wkm Exp] : τ2[wkm Exp] ⟩).
Proof.
  eapply abs_inversion'; eauto.
  eapply CoRefl.
  eapply tm_agreement_ty; eauto.
Qed.

(* Lemma abs_inversion {Γ S1 T1 T2 s2} (wΓ: wf_env Γ) *)
(*   (wt: Typing Γ (abs S1 s2) (tarr T1 T2)) : *)
(*   ⟨ Γ ⊢ T1 S1 star ∧ Typing (evar Γ S1) s2 T2. *)
(* Proof. *)
(*   apply abs_inversion' with (1 := wt); *)
(*     eauto using Q_Refl, typing_kinding. *)
(* Qed. *)

(* Lemma tyeq_tall_inversion {Γ J1 K1 S2 T2} : *)
(*   ⟨ Γ ⊢ (tall J1 S2) (tall K1 T2) star → *)
(*   J1 = K1 ∧ TyEq (etvar Γ K1) S2 T2 star. *)
(* Proof. *)
(*   intro q; destruct (teq_tred q) as [V [SV TV]]. *)
(*   destruct (tred_tall_preservation TV) as [V2' [Veq' T2V2]]. *)
(*   destruct (tred_tall_preservation SV) as [V2  [Veq S2V2]]; subst. *)
(*   dependent destruction Veq; split; auto; eapply (Q_Trans _ _ S2 V2); *)
(*     eauto with infra; [idtac | eapply Q_Symm]; *)
(*     eauto using tredstar_tyeq with infra. *)
(* Qed. *)

(* Lemma tabs_inversion' {Γ S J1 s2} (wt: Typing Γ (tyabs J1 s2) S) : *)
(*   ∀ K1 T2, ⟨ Γ ⊢ S (tall K1 T2) star → J1 = K1 ∧ Typing (etvar Γ K1) s2 T2. *)
(* Proof. *)
(*   depind wt; simpl; intros. *)
(*   - destruct (tyeq_tall_inversion H); subst; eauto 8 using T_Eq with infra. *)
(*   - apply IHwt; eauto using Q_Trans. *)
(* Qed. *)

(* Lemma tabs_inversion {Γ J1 K1 T2 s2} (wΓ: wf_env Γ) *)
(*   (wt: Typing Γ (tyabs J1 s2) (tall K1 T2)) : *)
(*   J1 = K1 ∧ Typing (etvar Γ J1) s2 T2. *)
(* Proof. *)
(*   assert (J1 = K1 ∧ Typing (etvar Γ K1) s2 T2). *)
(*   apply (tabs_inversion' wt); eauto using Q_Refl, typing_kinding. *)
(*   destruct_conjs; subst; auto. *)
(* Qed. *)

Lemma preservation {Γ t τ} (wΓ: WfEnv Γ) (clΓ: CoVarClosed Γ)
  (wt: ⟨ Γ ⊢ t : τ ⟩) :
  ∀ {t'}, t --> t' → ⟨ Γ ⊢ t' : τ ⟩.
Proof.
  induction wt; intros t' r; repeat crushIH.
  - inversion r.
  - inversion r.
  - inversion r.
  - inversion r.
  - inversion r; crush.
    + clear IHwt1 IHwt2.
      apply abs_inversion in wt1; eauto.
      destruct wt1 as ((γ1 & wγ1) & foo).
      (* Unset Printing Notations. *)
      idtac.
      admit.
    + clear IHwt1 IHwt2.
      pose proof (co_red H3 wΓ clΓ); crush.
      apply arr_consistency in H5; crush.
      admit.
  - admit.
  - admit.
  - admit.
Admitted.
