
Require Export SpecSyntax.

Reserved Notation "⟨ x : τ ∈ Γ ⟩"
  ( at level 0,
    x at level 98,
    τ at level 98,
    Γ at level 98).

Inductive GetTmVar : Env → Ix → Exp → Prop :=
  | tm_here {Γ τ} :
      ⟨   O : τ[wkm] ∈ Γ ▻ τ ⟩
  | tm_there_evar {Γ x τ τ'} :
      ⟨   x : τ      ∈ Γ      ⟩ →
      ⟨ S x : τ[wkm] ∈ Γ ▻ τ' ⟩
  | tm_there_τvar {Γ x τ k'} :
      ⟨   x : τ      ∈ Γ      ⟩ →
      ⟨ S x : τ[wkm] ∈ Γ ► k' ⟩
  | tm_there_γvar {Γ x τ τ1' τ2' k'} :
      ⟨   x : τ      ∈ Γ      ⟩ →
      ⟨ S x : τ[wkm] ∈ Γ ◅ τ1' ~ τ2' ∷ k' ⟩
where "⟨ x : τ ∈ Γ ⟩" := (GetTmVar Γ x τ).

Reserved Notation "⟨ α ∷ k ∈ Γ ⟩"
  ( at level 0,
    α at level 98,
    k at level 98,
    Γ at level 98).

Inductive GetTyVar : Env → Ix → Kind → Prop :=
  | ty_here {Γ k} :
      ⟨   O ∷ k ∈ Γ ► k ⟩
  | ty_there_evar {Γ α k τ'} :
      ⟨   α ∷ k ∈ Γ      ⟩ →
      ⟨ S α ∷ k ∈ Γ ▻ τ' ⟩
  | ty_there_τvar {Γ α k k'} :
      ⟨   α ∷ k ∈ Γ      ⟩ →
      ⟨ S α ∷ k ∈ Γ ► k' ⟩
  | ty_there_γvar {Γ α k τ1' τ2' k'} :
      ⟨   α ∷ k ∈ Γ      ⟩ →
      ⟨ S α ∷ k ∈ Γ ◅ τ1' ~ τ2' ∷ k' ⟩
where "⟨ α ∷ k ∈ Γ ⟩" := (GetTyVar Γ α k).

Reserved Notation "⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩"
  ( at level 0,
    c at level 98,
    τ1 at level 98,
    τ2 at level 98,
    k at level 98,
    Γ at level 98).

Inductive GetCoVar : Env → Ix → Exp → Exp → Kind → Prop :=
  | co_here {Γ τ1 τ2 k} :
      ⟨   O : τ1[wkm] ~ τ2[wkm] ∷ k ∈ Γ ◅ τ1 ~ τ2 ∷ k ⟩
  | co_there_evar {Γ c τ1 τ2 k τ'} :
      ⟨   c : τ1      ~ τ2      ∷ k ∈ Γ      ⟩ →
      ⟨ S c : τ1[wkm] ~ τ2[wkm] ∷ k ∈ Γ ▻ τ' ⟩
  | co_there_τvar {Γ c τ1 τ2 k k'} :
      ⟨   c : τ1      ~ τ2      ∷ k ∈ Γ      ⟩ →
      ⟨ S c : τ1[wkm] ~ τ2[wkm] ∷ k ∈ Γ ► k' ⟩
  | co_there_γvar {Γ c τ1 τ2 k τ1' τ2' k'} :
      ⟨   c : τ1      ~ τ2      ∷ k ∈ Γ      ⟩ →
      ⟨ S c : τ1[wkm] ~ τ2[wkm] ∷ k ∈ Γ ◅ τ1' ~ τ2' ∷ k' ⟩
where "⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩" := (GetCoVar Γ c τ1 τ2 k).

Reserved Notation "⟨ Γ ⊢ τ ∷ k ⟩"
  ( at level 0,
    Γ at level 98,
    τ at level 98,
    k at level 98).

Inductive Ty (Γ: Env) : Exp → Kind → Prop :=
  | TyVar {α k} :
      ⟨ α ∷ k ∈ Γ ⟩ →
      ⟨ Γ ⊢ var α ∷ k ⟩
  | TAbs {τ k1 k2} :
      ⟨ Γ ► k1 ⊢ τ ∷ k2 ⟩ →
      ⟨ Γ ⊢ τabs k1 τ ∷ karr k1 k2 ⟩
  | TApp {τ1 τ2 k1 k2}:
      ⟨ Γ ⊢ τ1 ∷ karr k1 k2 ⟩ →
      ⟨ Γ ⊢ τ2 ∷ k1 ⟩ →
      ⟨ Γ ⊢ τapp τ1 τ2 ∷ k2 ⟩
  | Arr {τ1 τ2} :
      ⟨ Γ ⊢ τ1 ∷ kstar ⟩ →
      ⟨ Γ ⊢ τ2 ∷ kstar ⟩ →
      ⟨ Γ ⊢ arr τ1 τ2 ∷ kstar ⟩
  | Arrτ {τ k} :
      ⟨ Γ ► k ⊢ τ ∷ kstar ⟩ →
      ⟨ Γ ⊢ arrτ k τ ∷ kstar ⟩
  | Arrγ {τ1 τ2 τ3 k} :
      ⟨ Γ ⊢ τ1 ∷ k ⟩ →
      ⟨ Γ ⊢ τ2 ∷ k ⟩ →
      ⟨ Γ ⊢ τ3 ∷ kstar ⟩ →
      ⟨ Γ ⊢ arrγ τ1 τ2 k τ3 ∷ kstar ⟩
where "⟨ Γ ⊢ τ ∷ k ⟩" := (Ty Γ τ k).

Reserved Notation "⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ k ⟩"
  ( at level 0,
    Γ at level 98,
    γ at level 98,
    τ1 at level 98,
    τ2 at level 98,
    k at level 98).

Inductive Co (Γ: Env) : Exp → Exp → Exp → Kind → Prop :=
  | CoVar {c τ1 τ2 k} :
      ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ →
      ⟨ Γ ⊢ var c : τ1 ~ τ2 ∷ k ⟩
  | CoTAbs {γ τ1 τ2 k1 k2} :
      ⟨ Γ ► k1 ⊢ γ : τ1 ~ τ2 ∷ k2 ⟩ →
      ⟨ Γ ⊢ coτabs k1 γ : τabs k1 τ1 ~ τabs k1 τ2 ∷ karr k1 k2 ⟩
  | CoTApp {γ1 γ2 τ11 τ12 τ21 τ22 k1 k2 }:
      ⟨ Γ ⊢ γ1 : τ11 ~ τ21 ∷ karr k1 k2 ⟩ →
      ⟨ Γ ⊢ γ2 : τ12 ~ τ22 ∷ k1 ⟩ →
      ⟨ Γ ⊢ coτapp γ1 γ2 : τapp τ11 τ12 ~ τapp τ21 τ22 ∷ k2 ⟩
  | CoArr {γ1 γ2 τ11 τ12 τ21 τ22}:
      ⟨ Γ ⊢ γ1 : τ11 ~ τ21 ∷ kstar ⟩ →
      ⟨ Γ ⊢ γ2 : τ12 ~ τ22 ∷ kstar ⟩ →
      ⟨ Γ ⊢ coarr γ1 γ2 : arr τ11 τ12 ~ arr τ21 τ22 ∷ kstar ⟩
  | CoArrτ {γ τ1 τ2 k} :
      ⟨ Γ ► k ⊢ γ : τ1 ~ τ2 ∷ kstar ⟩ →
      ⟨ Γ ⊢ coarrτ k γ : arrτ k τ1 ~ arrτ k τ2 ∷ kstar ⟩
  | CoArrγ {γ1 γ2 γ3 τ1 τ1' τ2 τ2' τ3 τ3' k} :
      ⟨ Γ ⊢ γ1 : τ1 ~ τ1' ∷ k ⟩ →
      ⟨ Γ ⊢ γ2 : τ2 ~ τ2' ∷ k ⟩ →
      ⟨ Γ ⊢ γ3 : τ3 ~ τ3' ∷ kstar ⟩ →
      ⟨ Γ ⊢ coarrγ γ1 γ2 k γ3 : arrγ τ1 τ2 k τ3 ~ arrγ τ1' τ2' k τ3' ∷ kstar ⟩
  | CoInvArr₁ {γ τ1 τ2 τ3 τ4}:
      ⟨ Γ ⊢ γ : arr τ1 τ2 ~ arr τ3 τ4 ∷ kstar ⟩ →
      ⟨ Γ ⊢ coinvarr₁ γ : τ1 ~ τ3 ∷ kstar ⟩
  | CoInvArr₂ {γ τ1 τ2 τ3 τ4}:
      ⟨ Γ ⊢ γ : arr τ1 τ2 ~ arr τ3 τ4 ∷ kstar ⟩ →
      ⟨ Γ ⊢ coinvarr₂ γ : τ2 ~ τ4 ∷ kstar ⟩
  | CoInvArrτ {γ1 γ2 τ1 τ2 τ3 τ4 k} :
      ⟨ Γ ⊢ γ1 : arrτ k τ1 ~ arrτ k τ2 ∷ kstar ⟩ →
      ⟨ Γ ⊢ γ2 : τ3 ~ τ4 ∷ k ⟩ →
      ⟨ Γ ⊢ coinvarrτ γ1 γ2 : τ1[beta1 τ3] ~ τ2[beta1 τ4] ∷ kstar ⟩
  | CoInvArrγ₁ {γ τ1 τ1' τ2 τ2' τ3 τ3' k} :
      ⟨ Γ ⊢ γ : arrγ τ1 τ2 k τ3 ~ arrγ τ1' τ2' k τ3' ∷ kstar ⟩ →
      ⟨ Γ ⊢ coinvarrγ₁ γ : τ1 ~ τ1' ∷ k ⟩
  | CoInvArrγ₂ {γ τ1 τ1' τ2 τ2' τ3 τ3' k} :
      ⟨ Γ ⊢ γ : arrγ τ1 τ2 k τ3 ~ arrγ τ1' τ2' k τ3' ∷ kstar ⟩ →
      ⟨ Γ ⊢ coinvarrγ₂ γ : τ2 ~ τ2' ∷ k ⟩
  | CoInvArrγ₃ {γ τ1 τ1' τ2 τ2' τ3 τ3' k} :
      ⟨ Γ ⊢ γ : arrγ τ1 τ2 k τ3 ~ arrγ τ1' τ2' k τ3' ∷ kstar ⟩ →
      ⟨ Γ ⊢ coinvarrγ₃ γ : τ3 ~ τ3' ∷ kstar ⟩
  | CoBeta {γ1 γ2 τ1 τ2 τ1' τ2' k1 k2} :
      ⟨ Γ ► k1 ⊢ γ1 : τ1 ~ τ1' ∷ k2 ⟩ →
      ⟨ Γ ⊢ γ2 : τ2 ~ τ2' ∷ k1 ⟩ →
      ⟨ Γ ⊢ cobeta k1 γ1 γ2 : τapp (τabs k1 τ1) τ2 ~ τ1'[beta1 τ2'] ∷ k2 ⟩
  | CoRefl {τ k} :
      ⟨ Γ ⊢ τ ∷ k ⟩ →
      ⟨ Γ ⊢ corefl τ : τ ~ τ ∷ k ⟩
  | CoSym {γ τ1 τ2 k} :
      ⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ k ⟩ →
      ⟨ Γ ⊢ cosym γ : τ2 ~ τ1 ∷ k ⟩
  | CoTrans {γ1 γ2 τ1 τ2 τ3 k} :
      ⟨ Γ ⊢ γ1 : τ1 ~ τ2 ∷ k ⟩ →
      ⟨ Γ ⊢ γ2 : τ2 ~ τ3 ∷ k ⟩ →
      ⟨ Γ ⊢ cotrans γ1 γ2 : τ1 ~ τ3 ∷ k ⟩
where "⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ k ⟩" := (Co Γ γ τ1 τ2 k).

Reserved Notation "⟨ Γ ⊢ γ : τ1 ↝ τ2 ∷ k ⟩"
  ( at level 0,
    Γ at level 98,
    γ at level 98,
    τ1 at level 98,
    τ2 at level 98,
    k at level 98).

Inductive Red (Γ: Env) : Exp → Exp → Exp → Kind → Prop :=
  | RedVar {c τ1 τ2 k} :
      ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ →
      ⟨ Γ ⊢ var c : τ1 ↝ τ2 ∷ k ⟩
  | RedTAbs {γ τ1 τ2 k1 k2} :
      ⟨ Γ ► k1 ⊢ γ : τ1 ↝ τ2 ∷ k2 ⟩ →
      ⟨ Γ ⊢ coτabs k1 γ : τabs k1 τ1 ↝ τabs k1 τ2 ∷ karr k1 k2 ⟩
  | RedTApp {γ1 γ2 τ11 τ12 τ21 τ22 k1 k2 }:
      ⟨ Γ ⊢ γ1 : τ11 ↝ τ21 ∷ karr k1 k2 ⟩ →
      ⟨ Γ ⊢ γ2 : τ12 ↝ τ22 ∷ k1 ⟩ →
      ⟨ Γ ⊢ coτapp γ1 γ2 : τapp τ11 τ12 ↝ τapp τ21 τ22 ∷ k2 ⟩
  | RedArr {γ1 γ2 τ11 τ12 τ21 τ22}:
      ⟨ Γ ⊢ γ1 : τ11 ↝ τ21 ∷ kstar ⟩ →
      ⟨ Γ ⊢ γ2 : τ12 ↝ τ22 ∷ kstar ⟩ →
      ⟨ Γ ⊢ coarr γ1 γ2 : arr τ11 τ12 ↝ arr τ21 τ22 ∷ kstar ⟩
  | RedArrτ {γ τ1 τ2 k} :
      ⟨ Γ ► k ⊢ γ : τ1 ↝ τ2 ∷ kstar ⟩ →
      ⟨ Γ ⊢ coarrτ k γ : arrτ k τ1 ↝ arrτ k τ2 ∷ kstar ⟩
  | RedArrγ {γ1 γ2 γ3 τ1 τ1' τ2 τ2' τ3 τ3' k} :
      ⟨ Γ ⊢ γ1 : τ1 ↝ τ1' ∷ k ⟩ →
      ⟨ Γ ⊢ γ2 : τ2 ↝ τ2' ∷ k ⟩ →
      ⟨ Γ ⊢ γ3 : τ3 ↝ τ3' ∷ kstar ⟩ →
      ⟨ Γ ⊢ coarrγ γ1 γ2 k γ3 : arrγ τ1 τ2 k τ3 ↝ arrγ τ1' τ2' k τ3' ∷ kstar ⟩
  | RedBeta {γ1 γ2 τ1 τ2 τ1' τ2' k1 k2} :
      ⟨ Γ ► k1 ⊢ γ1 : τ1 ↝ τ1' ∷ k2 ⟩ →
      ⟨ Γ ⊢ γ2 : τ2 ↝ τ2' ∷ k1 ⟩ →
      ⟨ Γ ⊢ cobeta k1 γ1 γ2 : τapp (τabs k1 τ1) τ2 ↝ τ1'[beta1 τ2'] ∷ k2 ⟩
  | RedReflVar {α k} :
      ⟨ α ∷ k ∈ Γ ⟩ →
      ⟨ Γ ⊢ corefl (var α) : var α ↝ var α ∷ k ⟩
where "⟨ Γ ⊢ γ : τ1 ↝ τ2 ∷ k ⟩" := (Red Γ γ τ1 τ2 k).

Reserved Notation "⟨ Γ ⊢ γs : τ1 ↝* τ2 ∷ k ⟩"
  ( at level 0,
    Γ at level 98,
    γs at level 98,
    τ1 at level 98,
    τ2 at level 98,
    k at level 98).

Inductive RedStar (Γ: Env) : list Exp → Exp → Exp → Kind → Prop :=
  | RedStarNil {τ k}:
      ⟨ Γ ⊢ τ ∷ k ⟩ →
      ⟨ Γ ⊢ nil : τ ↝* τ ∷ k ⟩
  | RedStarCons {τ1 τ2 τ3 γs γ k} :
      ⟨ Γ ⊢ γs : τ1 ↝* τ2 ∷ k ⟩ →
      ⟨ Γ ⊢ γ : τ2 ↝ τ3 ∷ k ⟩ →
      ⟨ Γ ⊢ cons γ γs : τ1 ↝* τ3 ∷ k ⟩
where "⟨ Γ ⊢ γs : τ1 ↝* τ2 ∷ k ⟩" := (RedStar Γ γs τ1 τ2 k).

Reserved Notation "⟨ Γ ⊢ s : τ ⟩"
  ( at level 0,
    Γ at level 98,
    s at level 98,
    τ at level 98).

Inductive Tm (Γ: Env) : Exp → Exp → Prop :=
  | Var {x τ} :
      ⟨ x : τ ∈ Γ ⟩ →
      ⟨ Γ ⊢ var x : τ ⟩
  | Abs {s τ1 τ2} :
      ⟨ Γ ⊢ τ1 ∷ kstar ⟩ →
      ⟨ Γ ▻ τ1 ⊢ s : τ2[wkm] ⟩ →
      ⟨ Γ ⊢ τ2 ∷ kstar ⟩ → (* Remove after adding strengthening lemmas *)
      ⟨ Γ ⊢ abs τ1 s : arr τ1 τ2 ⟩
  | Absτ {s τ k} :
      ⟨ Γ ► k ⊢ s : τ ⟩ →
      ⟨ Γ ⊢ absτ k s : arrτ k τ ⟩
  | Absγ {s τ1 τ2 τ3 k} :
      ⟨ Γ ◅ τ1 ~ τ2 ∷ k ⊢ s : τ3[wkm] ⟩ →
      ⟨ Γ ⊢ τ1 ∷ k ⟩ →
      ⟨ Γ ⊢ τ2 ∷ k ⟩ →
      ⟨ Γ ⊢ τ3 ∷ kstar ⟩ → (* Remove after adding strengthening lemmas *)
      ⟨ Γ ⊢ absγ τ1 τ2 k s : arrγ τ1 τ2 k τ3 ⟩
  | App {s1 s2 τ1 τ2} :
      ⟨ Γ ⊢ s1 : arr τ1 τ2 ⟩ →
      ⟨ Γ ⊢ s2 : τ1 ⟩ →
      ⟨ Γ ⊢ app s1 s2 : τ2 ⟩
  | Appτ {s τ1 τ2 k} :
      ⟨ Γ ⊢ s : arrτ k τ1 ⟩ →
      ⟨ Γ ⊢ τ2 ∷ k ⟩ →
      ⟨ Γ ⊢ appτ s τ2 : τ1[beta1 τ2] ⟩
  | Appγ {s γ τ1 τ2 τ3 k} :
      ⟨ Γ ⊢ s : arrγ τ1 τ2 k τ3 ⟩ →
      ⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ k ⟩ →
      ⟨ Γ ⊢ appγ s γ : τ3 ⟩
  | Cast {s γ τ1 τ2} :
      ⟨ Γ ⊢ s : τ1 ⟩ →
      ⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ kstar ⟩ →
      ⟨ Γ ⊢ cast s γ : τ2 ⟩
where "⟨ Γ ⊢ s : τ ⟩" := (Tm Γ s τ).
