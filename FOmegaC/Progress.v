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

Ltac canForm :=
  repeat
    (match goal with
       | [H: ⟨ _ ⊢ _ : _ ~ _ ∷ _ ⟩ |- _] =>
         eapply co_red in H
       | [H: ⟨ _ ⊢ _ : arr _ _ ↝ _ ∷ _ ⟩ |- _] =>
         inversion H; clear H
       | [H: ⟨ _ ⊢ _ : arr _ _ ↝* _ ∷ _ ⟩ |- _] =>
         eapply arr_consistency in H
       | [H: ⟨ _ ⊢ _ : arrτ _ _ ↝* _ ∷ _ ⟩ |- _] =>
         eapply arrτ_consistency in H
       | [H: ⟨ _ ⊢ _ : arrγ _ _ _ _ ↝* _ ∷ _ ⟩ |- _] =>
         eapply arrγ_consistency in H
     end; crush); eauto 20 with ws.

Lemma can_form_tarr' {t σ} (v: Value t) (wt: ⟨ nil ⊢ t : σ ⟩) :
  ∀ γ τ1 τ2,
    ⟨ nil ⊢ γ : σ ~ arr τ1 τ2 ∷ kstar ⟩ →
    (∃ t' τ1', t = abs τ1' t') ∨
    (∃ t' η τ1', t = cast (abs τ1' t') η).
Proof.
  depind wt; crush.
  - canForm.
  - canForm.
  - inversion wt; clear wt; crush.
    + pose proof (CoTrans nil H H0).
      canForm.
    + pose proof (CoTrans nil H H0).
      canForm.
Qed.

Lemma can_form_arr {t σ1 σ2} (v: Value t) (wt: ⟨ nil ⊢ t : arr σ1 σ2 ⟩) :
  (∃ t' τ', t = abs τ' t') ∨
  (∃ t' γ τ', t = cast (abs τ' t') γ).
Proof.
  eapply (can_form_tarr' v wt).
  eapply CoArr; eapply CoRefl;
    eapply tm_agreement_ty in wt; crush.
Qed.

Lemma can_form_arrτ' {t σ} (v: Value t) (wt: ⟨ nil ⊢ t : σ ⟩) :
  ∀ γ k τ,
    ⟨ nil ⊢ γ : σ ~ arrτ k τ ∷ kstar ⟩ →
    (∃ t', t = absτ k t') ∨
    (∃ t' η, t = cast (absτ k t') η).
Proof.
  depind wt; crush.
  - canForm.
  - canForm.
  - canForm.
  - inversion wt; clear wt; crush.
    + pose proof (CoTrans nil H H0).
      canForm.
    + pose proof (CoTrans nil H H0).
      canForm.
    + pose proof (CoTrans nil H H0).
      canForm.
Qed.

Lemma can_form_arrτ {t k σ} (v: Value t) (wt: ⟨ nil ⊢ t : arrτ k σ ⟩) :
  (∃ t', t = absτ k t') ∨
  (∃ t' γ, t = cast (absτ k t') γ).
Proof.
  eapply (can_form_arrτ' v wt).
  eapply CoArrτ; eapply CoRefl;
    eapply tm_agreement_ty in wt; crush.
Qed.


Lemma can_form_arrγ' {t σ} (v: Value t) (wt: ⟨ nil ⊢ t : σ ⟩) :
  ∀ γ k τ1 τ2 τ3,
    ⟨ nil ⊢ γ : σ ~ arrγ τ1 τ2 k τ3 ∷ kstar ⟩ →
    (∃ t' τ1' τ2', t = absγ τ1' τ2' k t') ∨
    (∃ t' η τ1' τ2', t = cast (absγ τ1' τ2' k t') η).
Proof.
  depind wt; crush.
  - canForm.
  - canForm.
  - canForm.
  - inversion wt; clear wt; crush.
    + pose proof (CoTrans nil H H0).
      canForm.
    + pose proof (CoTrans nil H H0).
      canForm.
    + pose proof (CoTrans nil H H0).
      canForm.
Qed.

Lemma can_form_arrγ {t σ1 σ2 k σ3} (v: Value t) (wt: ⟨ nil ⊢ t : arrγ σ1 σ2 k σ3 ⟩) :
  (∃ t' τ1' τ2', t = absγ τ1' τ2' k t') ∨
  (∃ t' γ τ1' τ2', t = cast (absγ τ1' τ2' k t') γ).
Proof.
  eapply (can_form_arrγ' v wt).
  eapply CoArrγ; eapply CoRefl;
    eapply tm_agreement_ty in wt; crush.
Qed.


Ltac progressMatch :=
  match goal with
    | [ |- False ∨ _ ] => right
    | [ |- True ∨ _ ] => left; trivial
    | [ H: _ ∨ _ |- _ ] => destruct H
    | [ vt: Value ?t, wt: ⟨ nil ⊢ ?t : arr _ _ ⟩ |- _ ] =>
      apply (can_form_arr vt) in wt
    | [ vt: Value ?t, wt: ⟨ nil ⊢ ?t : arrτ _ _ ⟩ |- _ ] =>
      apply (can_form_arrτ vt) in wt
    | [ vt: Value ?t, wt: ⟨ nil ⊢ ?t : arrγ _ _ _ _ ⟩ |- _ ] =>
      apply (can_form_arrγ vt) in wt
  end.

Lemma progress {t σ} (wt: ⟨ nil ⊢ t : σ ⟩) :
  Value t ∨ ∃ t', t --> t'.
Proof with destruct_conjs; subst*; eauto using eval.
  depind wt; intuition; crush; repeat progressMatch; crush; eauto using eval.
  - inversion wt; crush; eauto using eval.
Qed.
