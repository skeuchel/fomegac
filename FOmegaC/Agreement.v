Require Import Coq.Lists.List.
Require Export ParDB.Spec.
Require Export ParDB.Lemmas.
Require Export ParDB.Inst.

Require Export SpecSyntax.
Require Export SpecTyping.
Require Export LemmasTyping.

Local Ltac crush :=
  intros;
  repeat
    (cbn in *;
     (* repeat crushStlcSyntaxMatchH; *)
     repeat crushDbSyntaxMatchH;
     repeat crushDbLemmasRewriteH;
     repeat crushSyntaxRefold;
     repeat crushTypingMatchH;
     subst*;
     try discriminate;
     eauto 200 with ws;
     idtac
    ).

Lemma red_co {Γ γ σ τ k} :
  ⟨ Γ ⊢ γ : σ ↝ τ ∷ k ⟩ →
  ⟨ Γ ⊢ γ : σ ~ τ ∷ k ⟩.
Proof. induction 1; eauto using Co, Ty. Qed.
Hint Resolve red_co : ws.

Definition cofromredstar (σ: Exp) (γs: list Exp) : Exp :=
  fold_right (fun γ2 γ1 => cotrans γ1 γ2) (corefl σ) γs.

Lemma redstar_co {Γ γs σ τ k} :
  ⟨ Γ ⊢ γs : σ ↝* τ ∷ k ⟩ →
  ⟨ Γ ⊢ cofromredstar σ γs : σ ~ τ ∷ k ⟩.
Proof. induction 1; crush. Qed.
Hint Resolve redstar_co : ws.

Record WfEnv (Γ: Env) : Prop :=
  { wfenv_covar_kind_left : ∀ c σ τ k, ⟨ c : σ ~ τ ∷ k ∈ Γ ⟩ → ⟨ Γ ⊢ σ ∷ k ⟩;
    wfenv_covar_kind_right : ∀ c σ τ k, ⟨ c : σ ~ τ ∷ k ∈ Γ ⟩ → ⟨ Γ ⊢ τ ∷ k ⟩
  }.
Hint Resolve wfenv_covar_kind_left.
Hint Resolve wfenv_covar_kind_right.

Lemma wfenv_snoc_tyvar {Γ} (wΓ: WfEnv Γ) : ∀ k, WfEnv (Γ ► k).
Proof. constructor; crush; eauto with ws. Qed.
Hint Resolve wfenv_snoc_tyvar : ws.

Lemma co_agreement {Γ γ σ τ k} (wΓ: WfEnv Γ) (wγ: ⟨ Γ ⊢ γ : σ ~ τ ∷ k ⟩) :
  ⟨ Γ ⊢ σ ∷ k ⟩ ∧ ⟨ Γ ⊢ τ ∷ k ⟩.
Proof.
  induction wγ; intuition; crush;
  match goal with
    | [IH: WfEnv (?Γ ► ?k) → _ |- _] =>
      enough (WfEnv (Γ ► k)); intuition; crush
  end.
Qed.

Lemma co_agreement_left {Γ γ σ τ k} (wΓ: WfEnv Γ) (wγ: ⟨ Γ ⊢ γ : σ ~ τ ∷ k ⟩) :
  ⟨ Γ ⊢ σ ∷ k ⟩.
Proof. eapply co_agreement; eauto with ws. Qed.
Hint Resolve co_agreement_left : ws.

Lemma co_agreement_right {Γ γ σ τ k} (wΓ: WfEnv Γ) (wγ: ⟨ Γ ⊢ γ : σ ~ τ ∷ k ⟩) :
  ⟨ Γ ⊢ τ ∷ k ⟩.
Proof. eapply co_agreement; eauto with ws. Qed.
Hint Resolve co_agreement_right : ws.

(******************************************************************************)

Fixpoint redrefl (τ: Exp) : Exp :=
  match τ with
    | var α           => corefl (var α)
    | τabs k τ        => coτabs k (redrefl τ)
    | τapp τ1 τ2      => coτapp (redrefl τ1) (redrefl τ2)
    | arr τ1 τ2       => coarr (redrefl τ1) (redrefl τ2)
    | arrτ k τ        => coarrτ k (redrefl τ)
    | arrγ τ1 τ2 k τ3 => coarrγ (redrefl τ1) (redrefl τ2) k (redrefl τ3)
    | _ => var 0
  end.

Lemma RedRefl {Γ τ k} (wτ: ⟨ Γ ⊢ τ ∷ k ⟩) :
  ⟨ Γ ⊢ redrefl τ : τ ↝ τ ∷ k ⟩.
Proof. induction wτ; crush. Qed.
Hint Resolve RedRefl : ws.


Definition rstrans (γs1 γs2: list Exp) : list Exp :=
  List.app γs2 γs1.
Lemma RsTrans {Γ γs1 γs2 τ1 τ2 τ3 k} :
  ⟨ Γ ⊢ γs1 : τ1 ↝* τ2 ∷ k ⟩ →
  ⟨ Γ ⊢ γs2 : τ2 ↝* τ3 ∷ k ⟩ →
  ⟨ Γ ⊢ rstrans γs1 γs2 : τ1 ↝* τ3 ∷ k ⟩.
Proof. intros wγs1 wγs2; induction wγs2; crush. Qed.


Definition rsτabs (k: Kind) (γs: list Exp) : list Exp :=
  List.map (coτabs k) γs.
Lemma RsTAbs {Γ γs σ τ k1 k2} :
  ⟨ Γ ► k1 ⊢ γs : σ ↝* τ ∷ k2 ⟩ →
  ⟨ Γ ⊢ rsτabs k1 γs : τabs k1 σ ↝* τabs k1 τ ∷ karr k1 k2 ⟩.
Proof. intros wγs; depind wγs; crush. Qed.


Definition rsτapp₁ (γs: list Exp) (τ: Exp) : list Exp :=
  List.map (fun γ => coτapp γ (redrefl τ)) γs.
Definition rsτapp₂ (σ: Exp) (γs: list Exp)  : list Exp :=
  List.map (coτapp (redrefl σ)) γs.
Definition rsτapp (σγs: list Exp) (σ1 σ2: Exp) (τγs: list Exp) (τ1 τ2 : Exp) : list Exp :=
  rstrans (rsτapp₁ σγs τ1) (rsτapp₂ σ2 τγs).

Lemma RsTApp₁ {Γ γs σ1 σ2 τ k1 k2} :
  ⟨ Γ ⊢ γs : σ1 ↝* σ2 ∷ karr k1 k2 ⟩ →
  ⟨ Γ ⊢ τ ∷ k1 ⟩ →
  ⟨ Γ ⊢ rsτapp₁ γs τ : τapp σ1 τ ↝* τapp σ2 τ ∷ k2 ⟩.
Proof. intros wγs wτ; unfold rsτapp₁; depind wγs; crush. Qed.
Lemma RsTApp₂ {Γ γs τ1 τ2 σ k1 k2} :
  ⟨ Γ ⊢ σ ∷ karr k1 k2 ⟩ →
  ⟨ Γ ⊢ γs : τ1 ↝* τ2 ∷ k1 ⟩ →
  ⟨ Γ ⊢ rsτapp₂ σ γs: τapp σ τ1 ↝* τapp σ τ2 ∷ k2 ⟩.
Proof. intros wσ wγs; unfold rsτapp₂; depind wγs; crush. Qed.

Lemma RsTApp {Γ σγs τγs σ1 σ2 τ1 τ2 k1 k2} :
  ⟨ Γ ⊢ σ2 ∷ karr k1 k2 ⟩ →
  ⟨ Γ ⊢ σγs : σ1 ↝* σ2 ∷ karr k1 k2 ⟩ →
  ⟨ Γ ⊢ τ1 ∷ k1 ⟩ →
  ⟨ Γ ⊢ τγs : τ1 ↝* τ2 ∷ k1 ⟩ →
  ⟨ Γ ⊢ rsτapp σγs σ1 σ2 τγs τ1 τ2 : τapp σ1 τ1 ↝* τapp σ2 τ2 ∷ k2 ⟩.
Proof.
  intros.
  eapply RsTrans.
  - eapply RsTApp₁; crush.
  - eapply RsTApp₂; crush.
Qed.


Definition rsarr₁ (γs: list Exp) (τ: Exp) : list Exp :=
  List.map (fun γ => coarr γ (redrefl τ)) γs.
Definition rsarr₂ (σ: Exp) (γs: list Exp)  : list Exp :=
  List.map (coarr (redrefl σ)) γs.
Definition rsarr (σγs: list Exp) (σ1 σ2: Exp) (τγs: list Exp) (τ1 τ2 : Exp) : list Exp :=
  rstrans (rsarr₁ σγs τ1) (rsarr₂ σ2 τγs).

Lemma RsArr₁ {Γ σγs σ1 σ2 τ} :
  ⟨ Γ ⊢ σγs : σ1 ↝* σ2 ∷ kstar ⟩ →
  ⟨ Γ ⊢ τ ∷ kstar ⟩ →
  ⟨ Γ ⊢ rsarr₁ σγs τ : arr σ1 τ ↝* arr σ2 τ ∷ kstar ⟩.
Proof. intros wσγs wτ; unfold rsarr₁; depind wσγs; crush. Qed.
Lemma RsArr₂ {Γ σ τγs τ1 τ2} :
  ⟨ Γ ⊢ σ ∷ kstar ⟩ →
  ⟨ Γ ⊢ τγs : τ1 ↝* τ2 ∷ kstar ⟩ →
  ⟨ Γ ⊢ rsarr₂ σ τγs: arr σ τ1 ↝* arr σ τ2 ∷ kstar ⟩.
Proof. intros wσ wτγs; unfold rsarr₂; depind wτγs; crush. Qed.

Lemma RsArr {Γ σγs σ1 σ2 τγs τ1 τ2} :
  ⟨ Γ ⊢ σ2 ∷ kstar ⟩ →
  ⟨ Γ ⊢ σγs : σ1 ↝* σ2 ∷ kstar ⟩ →
  ⟨ Γ ⊢ τ1 ∷ kstar ⟩ →
  ⟨ Γ ⊢ τγs : τ1 ↝* τ2 ∷ kstar ⟩ →
  ⟨ Γ ⊢ rsarr σγs σ1 σ2 τγs τ1 τ2 : arr σ1 τ1 ↝* arr σ2 τ2 ∷ kstar ⟩.
Proof.
  intros.
  eapply RsTrans.
  - eapply RsArr₁; crush.
  - eapply RsArr₂; crush.
Qed.


Definition rsarrτ (k: Kind) (γs: list Exp) : list Exp :=
  List.map (coarrτ k) γs.
Lemma RsArrT {Γ γs σ τ k} :
  ⟨ Γ ► k ⊢ γs : σ ↝* τ ∷ kstar ⟩ →
  ⟨ Γ ⊢ rsarrτ k γs : arrτ k σ ↝* arrτ k τ ∷ kstar ⟩.
Proof. intros wγs; depind wγs; crush. Qed.


Definition rsarrγ₁ (σγs: list Exp) (τ: Exp) (k: Kind) (ν: Exp) : list Exp :=
  List.map (fun σγ => coarrγ σγ (redrefl τ) k (redrefl ν)) σγs.
Definition rsarrγ₂ (σ: Exp) (τγs: list Exp) (k: Kind) (ν: Exp) : list Exp :=
  List.map (fun τγ => coarrγ (redrefl σ) τγ k (redrefl ν)) τγs.
Definition rsarrγ₃ (σ: Exp) (τ: Exp) (k: Kind) (νγs: list Exp) : list Exp :=
  List.map (fun νγ => coarrγ (redrefl σ) (redrefl τ) k νγ) νγs.
Definition rsarrγ (σγs: list Exp) (σ σ': Exp) (τγs: list Exp) (τ τ': Exp) k (νγs: list Exp) (ν ν': Exp) : list Exp :=
  rstrans (rsarrγ₁ σγs τ k ν) (rstrans (rsarrγ₂ σ' τγs k ν) (rsarrγ₃ σ' τ' k νγs)).

Lemma RsArrG₁ {Γ σγs σ σ' τ k ν} :
  ⟨ Γ ⊢ σγs : σ ↝* σ' ∷ k ⟩ →
  ⟨ Γ ⊢ τ ∷ k ⟩ →
  ⟨ Γ ⊢ ν ∷ kstar ⟩ →
  ⟨ Γ ⊢ rsarrγ₁ σγs τ k ν : arrγ σ τ k ν ↝* arrγ σ' τ k ν ∷ kstar ⟩.
Proof. intros wσγs wτ wν; unfold rsarrγ₁; depind wσγs; crush. Qed.
Lemma RsArrG₂ {Γ σ τγs τ τ' k ν} :
  ⟨ Γ ⊢ σ ∷ k ⟩ →
  ⟨ Γ ⊢ τγs : τ ↝* τ' ∷ k ⟩ →
  ⟨ Γ ⊢ ν ∷ kstar ⟩ →
  ⟨ Γ ⊢ rsarrγ₂ σ τγs k ν : arrγ σ τ k ν ↝* arrγ σ τ' k ν ∷ kstar ⟩.
Proof. intros wσ wτγs wν; unfold rsarrγ₂; depind wτγs; crush. Qed.
Lemma RsArrG₃ {Γ σ τ k νγs ν ν'} :
  ⟨ Γ ⊢ σ ∷ k ⟩ →
  ⟨ Γ ⊢ τ ∷ k ⟩ →
  ⟨ Γ ⊢ νγs : ν ↝* ν' ∷ kstar ⟩ →
  ⟨ Γ ⊢ rsarrγ₃ σ τ k νγs : arrγ σ τ k ν ↝* arrγ σ τ k ν' ∷ kstar ⟩.
Proof. intros wσ wτ wνγs; unfold rsarrγ₃; depind wνγs; crush. Qed.

Lemma RsArrG {Γ σγs σ σ' τγs τ τ' k νγs ν ν'} :
  ⟨ Γ ⊢ σ' ∷ k ⟩ →
  ⟨ Γ ⊢ σγs : σ ↝* σ' ∷ k ⟩ →
  ⟨ Γ ⊢ τ ∷ k ⟩ →
  ⟨ Γ ⊢ τ' ∷ k ⟩ →
  ⟨ Γ ⊢ τγs : τ ↝* τ' ∷ k ⟩ →
  ⟨ Γ ⊢ ν ∷ kstar ⟩ →
  ⟨ Γ ⊢ νγs : ν ↝* ν' ∷ kstar ⟩ →
  ⟨ Γ ⊢ rsarrγ σγs σ σ' τγs τ τ' k νγs ν ν' : arrγ σ τ k ν ↝* arrγ σ' τ' k ν' ∷ kstar ⟩.
Proof.
  intros.
  eapply RsTrans.
  eapply RsArrG₁; crush.
  eapply RsTrans.
  eapply RsArrG₂; crush.
  eapply RsArrG₃; crush.
Qed.


Definition rsbeta (k: Kind) (σγs: list Exp) (σ σ': Exp) (τγs: list Exp) (τ τ': Exp) : list Exp :=
  cons (cobeta k (redrefl σ') (redrefl τ')) (rsτapp (rsτabs k σγs) (τabs k σ) (τabs k σ') τγs τ τ').

Lemma RsBeta {Γ σγs σ σ' τγs τ τ' k1 k2} :
  ⟨ Γ ► k1 ⊢ σ' ∷ k2 ⟩ →
  ⟨ Γ ► k1 ⊢ σγs : σ ↝* σ' ∷ k2 ⟩ →
  ⟨ Γ ⊢ τ ∷ k1 ⟩ →
  ⟨ Γ ⊢ τ' ∷ k1 ⟩ →
  ⟨ Γ ⊢ τγs : τ ↝* τ' ∷ k1 ⟩ →
  ⟨ Γ ⊢ rsbeta k1 σγs σ σ' τγs τ τ' : τapp (τabs k1 σ) τ ↝* σ'[beta1 τ'] ∷ k2 ⟩.
Proof.
  intros. unfold rsbeta.
  econstructor.
  - eapply RsTApp; eauto.
    + constructor; auto.
    + eapply RsTAbs; eauto.
  - constructor; eauto.
    + eapply RedRefl; eauto.
    + eapply RedRefl; eauto.
Qed.


(* Definition coredstarbeta₁ (k: Kind) (γs: list Exp) (τ: Exp) : list Exp := *)
(*   List.map (fun γ => cobeta k γ (redrefl τ)) γs. *)
(* Lemma RedStarBeta₁ {Γ γsσ σ σ' γsτ τ τ' k1 k2} : *)
(*   ⟨ Γ ► k1 ⊢ γsσ : σ ↝* σ' ∷ k2 ⟩ → *)
(*   ⟨ Γ ⊢ γsτ : τ ~ τ' ∷ k1 ⟩ → *)
(*   ∃ ηs, ⟨ Γ ⊢ ηs : τapp (τabs k1 σ) τ ↝* σ'[beta1 τ'] ∷ k2 ⟩. *)
(* Proof.   *)
(*   unfold coredstarbeta₁; depind rσ; crush. *)
(* Qed. *)

(* Definition coredstarbeta₂ (σ: Exp) (γs: list Exp)  : list Exp := *)
(*   List.map (cobeta (redrefl σ)) γs. *)
(* Lemma RedStarBeta₂ {Γ γs τ1 τ2} (rτ: ⟨ Γ ⊢ γs : τ1 ↝* τ2 ∷ kstar ⟩) : *)
(*   ∀ {σ}, ⟨ Γ ⊢ σ ∷ kstar ⟩ → ⟨ Γ ⊢ coredstarbeta₂ σ γs: beta σ τ1 ↝* beta σ τ2 ∷ kstar ⟩. *)
(* Proof. unfold coredstarbeta₂; depind rτ; crush. Qed. *)

(* Definition coredstarbeta (σγs: list Exp) (σ1 σ2: Exp) (τγs: list Exp) (τ1 τ2 : Exp) : list Exp := *)
(*   rstrans (coredstarbeta₁ σγs τ1) (coredstarbeta₂ σ2 τγs). *)
(* Lemma RedStarBeta {Γ σγs τγs σ1 σ2 τ1 τ2} (wΓ: WfEnv Γ) *)
(*   (wσγs: ⟨ Γ ⊢ σγs : σ1 ↝* σ2 ∷ kstar ⟩) *)
(*   (wτγs: ⟨ Γ ⊢ τγs : τ1 ↝* τ2 ∷ kstar ⟩) : *)
(*   ⟨ Γ ⊢ coredstarbeta σγs σ1 σ2 τγs τ1 τ2 : beta σ1 τ1 ↝* beta σ2 τ2 ∷ kstar ⟩. *)
(* Proof. *)
(*   eapply RsTrans. *)
(*   - eapply RedStarBeta₁; crush. *)
(*   - eapply RedStarBeta₂; crush. *)
(* Qed. *)

(*
Definition rstrans (γs1 γs2: list Exp) : list Exp :=
  List.app γs2 γs1.

Lemma RsTrans {Γ γs1 γs2 τ1 τ2 ν k} :
  ⟨ Γ ⊢ γs1 : τ1 ↝* τ2 ∷ k ⟩ →
  ⟨ Γ ⊢ γs2 : τ2 ↝* ν ∷ k ⟩ →
  ⟨ Γ ⊢ rstrans γs1 γs2 : τ1 ↝* τ3 ∷ k ⟩.
Proof. intros r q; revert τ1 r; induction q; crush. Qed.

Fixpoint redrefl (τ: Exp) : Exp :=
  match τ with
    | var α           => corefl (var α)
    | τabs k τ        => coτabs k (redrefl τ)
    | τapp τ1 τ2      => coτapp (redrefl τ1) (redrefl τ2)
    | arr τ1 τ2       => coarr (redrefl τ1) (redrefl τ2)
    | arrτ k τ        => coarrτ k (redrefl τ)
    | arrγ τ1 τ2 k τ3 => coarrγ (redrefl τ1) (redrefl τ2) k (redrefl τ3)
    | _ => var 0
  end.

Lemma RedRefl {Γ τ k} (wτ: ⟨ Γ ⊢ τ ∷ k ⟩) :
  ⟨ Γ ⊢ redrefl τ : τ ↝ τ ∷ k ⟩.
Proof. induction wτ; crush. Qed.
Hint Resolve RedRefl : ws.

Definition rsτapp₁ (γs: list Exp) (τ: Exp) : list Exp :=
  List.map (fun γ => coτapp γ (redrefl τ)) γs.
Lemma RsTApp₁ {Γ γs σ1 σ2 k1 k2} (rσ: ⟨ Γ ⊢ γs : σ1 ↝* σ2 ∷ karr k1 k2 ⟩) :
  ∀ {τ}, ⟨ Γ ⊢ τ ∷ k1 ⟩ → ⟨ Γ ⊢ rsτapp₁ γs τ : τapp σ1 τ ↝* τapp σ2 τ ∷ k2 ⟩.
Proof. unfold rsτapp₁; depind rσ; crush. Qed.
Definition rsτapp₂ (σ: Exp) (γs: list Exp)  : list Exp :=
  List.map (coτapp (redrefl σ)) γs.
Lemma RsTApp₂ {Γ γs τ1 τ2 k1} (rτ: ⟨ Γ ⊢ γs : τ1 ↝* τ2 ∷ k1 ⟩) :
  ∀ {σ k2}, ⟨ Γ ⊢ σ ∷ karr k1 k2 ⟩ → ⟨ Γ ⊢ rsτapp₂ σ γs: τapp σ τ1 ↝* τapp σ τ2 ∷ k2 ⟩.
Proof. unfold rsτapp₂; depind rτ; crush. Qed.

Definition rsτapp (σγs: list Exp) (σ1 σ2: Exp) (τγs: list Exp) (τ1 τ2 : Exp) : list Exp :=
  rstrans (rsτapp₁ σγs τ1) (rsτapp₂ σ2 τγs).
Lemma RsTApp {Γ σγs τγs σ1 σ2 τ1 τ2 k1 k2} (wΓ: WfEnv Γ)
  (wσγs: ⟨ Γ ⊢ σγs : σ1 ↝* σ2 ∷ karr k1 k2 ⟩)
  (wτγs: ⟨ Γ ⊢ τγs : τ1 ↝* τ2 ∷ k1 ⟩) :
  ⟨ Γ ⊢ rsτapp σγs σ1 σ2 τγs τ1 τ2 : τapp σ1 τ1 ↝* τapp σ2 τ2 ∷ k2 ⟩.
Proof.
  eapply RsTrans.
  - eapply RsTApp₁; crush.
  - eapply RsTApp₂; crush.
Qed.

Definition rsτabs (k: Kind) (γs: list Exp) : list Exp :=
  List.map (coτabs k) γs.
Lemma RsTAbs {Γ γs σ τ k1 k2} :
  ⟨ Γ ► k1 ⊢ γs : σ ↝* τ ∷ k2 ⟩ →
  ⟨ Γ ⊢ rsτabs k1 γs : τabs k1 σ ↝* τabs k1 τ ∷ karr k1 k2 ⟩.
Proof. intros wγs; depind wγs; crush. Qed.


Definition rsarr₁ (γs: list Exp) (τ: Exp) : list Exp :=
  List.map (fun γ => coarr γ (redrefl τ)) γs.
Lemma RsArr₁ {Γ γs σ1 σ2} (rσ: ⟨ Γ ⊢ γs : σ1 ↝* σ2 ∷ kstar ⟩) :
  ∀ {τ}, ⟨ Γ ⊢ τ ∷ kstar ⟩ → ⟨ Γ ⊢ rsarr₁ γs τ : arr σ1 τ ↝* arr σ2 τ ∷ kstar ⟩.
Proof. unfold rsarr₁; depind rσ; crush. Qed.
Definition rsarr₂ (σ: Exp) (γs: list Exp)  : list Exp :=
  List.map (coarr (redrefl σ)) γs.
Lemma RsArr₂ {Γ γs τ1 τ2} (rτ: ⟨ Γ ⊢ γs : τ1 ↝* τ2 ∷ kstar ⟩) :
  ∀ {σ}, ⟨ Γ ⊢ σ ∷ kstar ⟩ → ⟨ Γ ⊢ rsarr₂ σ γs: arr σ τ1 ↝* arr σ τ2 ∷ kstar ⟩.
Proof. unfold rsarr₂; depind rτ; crush. Qed.

Definition rsarr (σγs: list Exp) (σ1 σ2: Exp) (τγs: list Exp) (τ1 τ2 : Exp) : list Exp :=
  rstrans (rsarr₁ σγs τ1) (rsarr₂ σ2 τγs).
Lemma RsArr {Γ σγs τγs σ1 σ2 τ1 τ2} (wΓ: WfEnv Γ)
  (wσγs: ⟨ Γ ⊢ σγs : σ1 ↝* σ2 ∷ kstar ⟩)
  (wτγs: ⟨ Γ ⊢ τγs : τ1 ↝* τ2 ∷ kstar ⟩) :
  ⟨ Γ ⊢ rsarr σγs σ1 σ2 τγs τ1 τ2 : arr σ1 τ1 ↝* arr σ2 τ2 ∷ kstar ⟩.
Proof.
  eapply RsTrans.
  - eapply RsArr₁; crush.
  - eapply RsArr₂; crush.
Qed.


(* Definition rsarrτ (k: Kind) (γs: list Exp) : list Exp := *)
(*   List.map (coarrτ k) γs. *)
(* Lemma RsArrT {Γ γs σ τ k} : *)
(*   ⟨ Γ ► k ⊢ γs : σ ↝* τ ∷ kstar ⟩ → *)
(*   ⟨ Γ ⊢ rsarrτ k γs : arrτ k σ ↝* arrτ k τ ∷ kstar ⟩. *)
(* Proof. intros wγs; depind wγs; crush. Qed. *)


(* Definition coredstarbeta₁ (k: Kind) (γs: list Exp) (τ: Exp) : list Exp := *)
(*   List.map (fun γ => cobeta k γ (redrefl τ)) γs. *)
(* Lemma RedStarBeta₁ {Γ γsσ σ σ' γsτ τ τ' k1 k2} : *)
(*   ⟨ Γ ► k1 ⊢ γsσ : σ ↝* σ' ∷ k2 ⟩ → *)
(*   ⟨ Γ ⊢ γsτ : τ ~ τ' ∷ k1 ⟩ → *)
(*   ∃ ηs, ⟨ Γ ⊢ ηs : τapp (τabs k1 σ) τ ↝* σ'[beta1 τ'] ∷ k2 ⟩. *)
(* Proof.   *)
(*   unfold coredstarbeta₁; depind rσ; crush. *)
(* Qed. *)

(* Definition coredstarbeta₂ (σ: Exp) (γs: list Exp)  : list Exp := *)
(*   List.map (cobeta (redrefl σ)) γs. *)
(* Lemma RedStarBeta₂ {Γ γs τ1 τ2} (rτ: ⟨ Γ ⊢ γs : τ1 ↝* τ2 ∷ kstar ⟩) : *)
(*   ∀ {σ}, ⟨ Γ ⊢ σ ∷ kstar ⟩ → ⟨ Γ ⊢ coredstarbeta₂ σ γs: beta σ τ1 ↝* beta σ τ2 ∷ kstar ⟩. *)
(* Proof. unfold coredstarbeta₂; depind rτ; crush. Qed. *)

(* Definition coredstarbeta (σγs: list Exp) (σ1 σ2: Exp) (τγs: list Exp) (τ1 τ2 : Exp) : list Exp := *)
(*   rstrans (coredstarbeta₁ σγs τ1) (coredstarbeta₂ σ2 τγs). *)
(* Lemma RedStarBeta {Γ σγs τγs σ1 σ2 τ1 τ2} (wΓ: WfEnv Γ) *)
(*   (wσγs: ⟨ Γ ⊢ σγs : σ1 ↝* σ2 ∷ kstar ⟩) *)
(*   (wτγs: ⟨ Γ ⊢ τγs : τ1 ↝* τ2 ∷ kstar ⟩) : *)
(*   ⟨ Γ ⊢ coredstarbeta σγs σ1 σ2 τγs τ1 τ2 : beta σ1 τ1 ↝* beta σ2 τ2 ∷ kstar ⟩. *)
(* Proof. *)
(*   eapply RsTrans. *)
(*   - eapply RedStarBeta₁; crush. *)
(*   - eapply RedStarBeta₂; crush. *)
(* Qed. *)
*)