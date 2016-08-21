Require Export SpecSyntax.
Require Export SpecTyping.

(*************************************************************************)
(* Evaluation.                                                           *)
(*************************************************************************)

Definition Value (t: Exp) : Prop :=
  match t with
    | abs τ s        => True
    | absτ k s       => True
    | absγ τ1 τ2 k s => True
    | cast (abs τ s) γ        => True
    | cast (absτ k s) γ       => True
    | cast (absγ τ1 τ2 k s) γ => True
    | _              => False
  end.



(* Reserved Notation "γ ──> γ'" (at level 55). *)
(* Inductive evalco : Exp → Exp → Prop := *)
(*   | eval_cong_coτabs {k γ γ'} : *)
(*       γ ──> γ' → *)
(*       coτabs k γ ──> coτabs k γ *)
(*   | eval_cong_coτapp₁ {γ1 γ1' γ2} : *)
(*       γ1 ──> γ1' → *)
(*       coτapp γ1 γ2 ──> coτapp γ1' γ2 *)
(*   | eval_cong_coτapp₂ {γ1 γ2 γ2'} : *)
(*       γ2 ──> γ2' → *)
(*       coτapp γ1 γ2 ──> coτapp γ1 γ2' *)
(*   | eval_cong_coarr₁ {γ1 γ1' γ2} : *)
(*       γ1 ──> γ1' → *)
(*       coarr γ1 γ2 ──> coarr γ1' γ2 *)
(*   | eval_cong_coarr₂ {γ1 γ2 γ2'} : *)
(*       γ2 ──> γ2' → *)
(*       coarr γ1 γ2 ──> coarr γ1 γ2' *)
(*   | eval_cong_coarrτ {k γ γ'} : *)
(*       γ ──> γ' → *)
(*       coarrτ k γ ──> coarrτ k γ' *)
(*   | eval_cong_coarrγ₁ {γ1 γ1' γ2 k γ3} : *)
(*       γ1 ──> γ1' → *)
(*       coarrγ γ1 γ2 k γ3 ──> coarrγ γ1' γ2 k γ3 *)
(*   | eval_cong_coarrγ₂ {γ1 γ2 γ2' k γ3} : *)
(*       γ2 ──> γ2' → *)
(*       coarrγ γ1 γ2 k γ3 ──> coarrγ γ1 γ2' k γ3 *)
(*   | eval_cong_coarrγ₃ {γ1 γ2 k γ3 γ3'} : *)
(*       γ3 ──> γ3' → *)
(*       coarrγ γ1 γ2 k γ3 ──> coarrγ γ1 γ2 k γ3' *)
(*   | eval_cong_coinvarr₁ {γ γ'} : *)
(*       γ ──> γ' → *)
(*       coinvarr₁ γ ──> coinvarr₁ γ' *)
(*   | eval_cong_coinvarr₂ {γ γ'} : *)
(*       γ ──> γ' → *)
(*       coinvarr₂ γ ──> coinvarr₂ γ' *)
(*   | eval_cong_coinvarrτ₁ {γ1 γ1' γ2} : *)
(*       γ1 ──> γ1' → *)
(*       coinvarrτ γ1 γ2 ──> coinvarrτ γ1' γ2 *)
(*   | eval_cong_coinvarrτ₂ {γ1 γ2 γ2'} : *)
(*       γ2 ──> γ2' → *)
(*       coinvarrτ γ1 γ2 ──> coinvarrτ γ1 γ2' *)
(*   | eval_cong_coinvarrγ₁ {γ γ'} : *)
(*       γ ──> γ' → *)
(*       coinvarrγ₁ γ ──> coinvarrγ₁ γ' *)
(*   | eval_cong_coinvarrγ₂ {γ γ'} : *)
(*       γ ──> γ' → *)
(*       coinvarrγ₂ γ ──> coinvarrγ₂ γ' *)
(*   | eval_cong_coinvarrγ₃ {γ γ'} : *)
(*       γ ──> γ' → *)
(*       coinvarrγ₃ γ ──> coinvarrγ₃ γ' *)
(*   | eval_cong_cobeta₁ {γ1 γ1' γ2} : *)
(*       γ1 ──> γ1' → *)
(*       cobeta γ1 γ2 ──> cobeta γ1' γ2 *)
(*   | eval_cong_cobeta₂ {γ1 γ2 γ2'} : *)
(*       γ2 ──> γ2' → *)
(*       cobeta γ1 γ2 ──> cobeta γ1 γ2' *)
(*   | eval_cong_cosym {γ γ'} : *)
(*       γ ──> γ' → *)
(*       cosym γ ──> cosym γ' *)
(*   | eval_cong_cotrans₁ {γ1 γ1' γ2} : *)
(*       γ1 ──> γ1' → *)
(*       cotrans γ1 γ2 ──> cotrans γ1' γ2 *)
(*   | eval_cong_cotrans₂ {γ1 γ2 γ2'} : *)
(*       γ2 ──> γ2' → *)
(*       cotrans γ1 γ2 ──> cotrans γ1 γ2' *)
(*   | eval_sym_coarr {γ1 γ2} : *)
(*       cosym (coarr γ1 γ2)  ──> coarr (cosym γ1) (cosym γ2) *)
(*   | eval_sym_coarrτ {k γ} : *)
(*       cosym (coarrτ k γ)  ──> coarrτ k (cosym γ) *)
(*   | eval_sym_coarrγ {γ1 γ2 k γ3} : *)
(*       cosym (coarrγ γ1 γ2 k γ3)  ──> coarrγ (cosym γ1) (cosym γ2) k (cosym γ3) *)
(*   | eval_sym_corefl {τ} : *)
(*       cosym (corefl τ)  ──> corefl τ *)
(*   | eval_trans_coarr {γ1 γ2 γ1' γ2'} : *)
(*       cotrans (coarr γ1 γ2) (coarr γ1' γ2')  ──> coarr (cotrans γ1 γ1') (cotrans γ2 γ2') *)
(*   | eval_trans_coarrτ {k γ γ'} : *)
(*       cotrans (coarrτ k γ) (coarrτ k γ')  ──> coarrτ k (cotrans γ γ') *)
(*   | eval_trans_coarrγ {γ1 γ2 k γ3 γ1' γ2' γ3'} : *)
(*       cotrans (coarrγ γ1 γ2 k γ3) (coarrγ γ1' γ2' k γ3')  ──> coarrγ (cotrans γ1 γ1') (cotrans γ2 γ2') k (cotrans γ3 γ3') *)
(*   | eval_trans_corefl₁ {τ γ} : *)
(*       cotrans (corefl τ) γ  ──> γ *)
(*   | eval_trans_corefl {τ γ} : *)
(*       cotrans γ (corefl τ)  ──> γ *)
(*   | eval_elim_coinvarr₁  {γ1 γ2} : *)
(*       coinvarr₁ (coarr γ1 γ2) ──> γ1 *)
(*   | eval_elim_coinvarr₂  {γ1 γ2} : *)
(*       coinvarr₂ (coarr γ1 γ2) ──> γ2 *)
(*   (* | eval_elim_coinvarrτ  {k γ1 γ2} : *) *)
(*   (*     coinvarrτ (coarrτ k γ1) γ2 ──> apCoSub [beta1 γ] *) *)
(*   | eval_elim_coinvarrγ₁ {γ1 γ2 k γ3} : *)
(*       coinvarrγ₁ (coarrγ γ1 γ2 k γ3)  ──> γ1 *)
(*   | eval_elim_coinvarrγ₂ {γ1 γ2 k γ3} : *)
(*       coinvarrγ₂ (coarrγ γ1 γ2 k γ3)  ──> γ2 *)
(*   | eval_elim_coinvarrγ₃ {γ1 γ2 k γ3} : *)
(*       coinvarrγ₃ (coarrγ γ1 γ2 k γ3)  ──> γ3 *)
(* where "γ ──> γ'" := (evalco γ γ'). *)


Reserved Notation "t --> t'" (at level 55).
Inductive eval : Exp → Exp → Prop :=
  | eval_app₁ {t1 t1' t2} :
      t1 --> t1' → app t1 t2 --> app t1' t2
  | eval_app₂ {t1 t2 t2'} :
      t2 --> t2' → app t1 t2 --> app t1 t2'
  | eval_beta {t1 t2 τ} :
      app (abs τ t1) t2 --> t1[beta1 t2]
  | eval_appτ₁ {t t' τ} :
      t --> t' → appτ t τ --> appτ t' τ
  | eval_betaτ {t τ k} :
      appτ (absτ k t) τ --> t[beta1 τ]
  | eval_appγ {t t' γ} :
      t --> t' → appγ t γ --> appτ t' γ
  | eval_betaγ {t γ τ1 τ2 k} :
      appγ (absγ τ1 τ2 k t) γ --> t[beta1 γ]
  | eval_cast {t t' γ} :
      t --> t' →
      cast t γ --> cast t' γ
  | eval_push_app_cast {t1 t2 γ} :
      app (cast t1 γ) t2 -->
        cast (app t1 (cast t2 (cosym (coinvarr₁ γ)))) (coinvarr₂ γ)
  | eval_push_appτ_cast {t τ γ} :
      appτ (cast t γ) τ -->
        cast (appτ t τ) (coinvarrτ γ (corefl τ))
  | eval_push_appγ_cast {t γ γ'} :
      appγ (cast t γ) γ' -->
        cast (appγ t (cotrans (coinvarrγ₁ γ) (cotrans γ' (cosym (coinvarrγ₂ γ))))) (coinvarrγ₃ γ)
     (*    appγ t (nth¹ γ ; γ' ; sym (nth² γ)) ▹ nth³ γ *)
     (* t             : (σ1 ~ τ1) => ρ1 *)
     (* γ             : ((σ1 ~ τ1) => ρ1) ~ ((σ2 ~ τ2) => ρ2) *)
     (* t ▹ γ         : (σ2 ~ τ2) => ρ2 *)
     (* γ'            : (σ2 ~ τ2) *)
     (* (t ▹ γ) γ'    : ρ2 *)
     (* nth¹ γ        : σ1 ~ σ2 *)
     (* nth² γ        : τ1 ~ τ2 *)
     (* nth³ γ        : ρ1 ~ ρ2 *)
  | eval_cast_cat {t η γ} :
      cast (cast t η) γ -->
        cast t (cotrans η γ)
where "t --> t'" := (eval t t').
