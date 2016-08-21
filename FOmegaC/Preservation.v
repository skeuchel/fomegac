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

Lemma preservation {Γ t τ} (wΓ: WfEnv Γ) (clΓ: CoVarClosed Γ)
  (wt: ⟨ Γ ⊢ t : τ ⟩) :
  ∀ {t'}, t --> t' → ⟨ Γ ⊢ t' : τ ⟩.
Proof.
  induction wt; intros t' r; repeat crushIH; inversion r; crush;
  try
    match goal with
      | H: UValue ?t |- _ => destruct t; crush
    end;
  try (consistency; crush; fail);
  try (repeat (econstructor; crush); fail).
  - replace τ2 with τ2[wkm Exp][beta1 s2] by crush.
    eapply tm_sub; crush.
    constructor; crush.
  - assert (k0 = k) by consistency; subst k0.
    repeat (econstructor; crush).
  - replace τ3 with τ3[wkm Exp][beta1 γ] by crush.
    eapply tm_sub; crush.
    constructor; crush.
  - assert (k0 = k) by consistency; subst k0.
    repeat (econstructor; crush).
Qed.
