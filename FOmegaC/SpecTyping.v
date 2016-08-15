
Require Export SpecSyntax.

Reserved Notation "⟨ x : τ ∈ Γ ⟩"
  ( at level 0,
    x at level 98,
    τ at level 98,
    Γ at level 98).

Inductive GetEVar : Env → Ix → Tm → Prop :=
  | ge_here {Γ τ} :
      ⟨   O : τ[wkm] ∈ Γ ▻ τ ⟩
  | ge_there_evar {Γ x τ τ'} :
      ⟨   x : τ      ∈ Γ      ⟩ →
      ⟨ S x : τ[wkm] ∈ Γ ▻ τ' ⟩
  | ge_there_τvar {Γ x τ k'} :
      ⟨   x : τ      ∈ Γ      ⟩ →
      ⟨ S x : τ[wkm] ∈ Γ ► k' ⟩
  | ge_there_γvar {Γ x τ τ1' τ2' k'} :
      ⟨   x : τ      ∈ Γ      ⟩ →
      ⟨ S x : τ[wkm] ∈ Γ ◅ τ1' ~ τ2' ∷ k' ⟩
where "⟨ x : τ ∈ Γ ⟩" := (GetEVar Γ x τ).

Reserved Notation "⟨ α ∷ k ∈ Γ ⟩"
  ( at level 0,
    α at level 98,
    k at level 98,
    Γ at level 98).

Inductive GetTVar : Env → Ix → Kind → Prop :=
  | gt_here {Γ k} :
      ⟨   O ∷ k ∈ Γ ► k ⟩
  | gt_there_evar {Γ α k τ'} :
      ⟨   α ∷ k ∈ Γ      ⟩ →
      ⟨ S α ∷ k ∈ Γ ▻ τ' ⟩
  | gt_there_τvar {Γ α k k'} :
      ⟨   α ∷ k ∈ Γ      ⟩ →
      ⟨ S α ∷ k ∈ Γ ► k' ⟩
  | gt_there_γvar {Γ α k τ1' τ2' k'} :
      ⟨   α ∷ k ∈ Γ      ⟩ →
      ⟨ S α ∷ k ∈ Γ ◅ τ1' ~ τ2' ∷ k' ⟩
where "⟨ α ∷ k ∈ Γ ⟩" := (GetTVar Γ α k).

Reserved Notation "⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩"
  ( at level 0,
    c at level 98,
    τ1 at level 98,
    τ2 at level 98,
    k at level 98,
    Γ at level 98).

Inductive GetCVar : Env → Ix → Tm → Tm → Kind → Prop :=
  | gc_here {Γ τ1 τ2 k} :
      ⟨   O : τ1[wkm] ~ τ2[wkm] ∷ k ∈ Γ ◅ τ1 ~ τ2 ∷ k ⟩
  | gc_there_evar {Γ c τ1 τ2 k τ'} :
      ⟨   c : τ1      ~ τ2      ∷ k ∈ Γ      ⟩ →
      ⟨ S c : τ1[wkm] ~ τ2[wkm] ∷ k ∈ Γ ▻ τ' ⟩
  | gc_there_τvar {Γ c τ1 τ2 k k'} :
      ⟨   c : τ1      ~ τ2      ∷ k ∈ Γ      ⟩ →
      ⟨ S c : τ1[wkm] ~ τ2[wkm] ∷ k ∈ Γ ► k' ⟩
  | gc_there_γvar {Γ c τ1 τ2 k τ1' τ2' k'} :
      ⟨   c : τ1      ~ τ2      ∷ k ∈ Γ      ⟩ →
      ⟨ S c : τ1[wkm] ~ τ2[wkm] ∷ k ∈ Γ ◅ τ1' ~ τ2' ∷ k' ⟩
where "⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩" := (GetCVar Γ c τ1 τ2 k).

Reserved Notation "⟨ Γ ⊢ τ ∷ k ⟩"
  ( at level 0,
    Γ at level 98,
    τ at level 98,
    k at level 98).

Inductive OfKind (Γ: Env) : Tm → Kind → Prop :=
  | K_tvar {α k} :
      ⟨ α ∷ k ∈ Γ ⟩ →
      ⟨ Γ ⊢ var α ∷ k ⟩
  | K_absττ {τ k1 k2} :
      ⟨ Γ ► k1 ⊢ τ ∷ k2 ⟩ →
      ⟨ Γ ⊢ absττ k1 τ ∷ karr k1 k2 ⟩
  | K_appττ {τ1 τ2 k1 k2}:
      ⟨ Γ ⊢ τ1 ∷ karr k1 k2 ⟩ →
      ⟨ Γ ⊢ τ2 ∷ k1 ⟩ →
      ⟨ Γ ⊢ appττ τ1 τ2 ∷ k2 ⟩
  | K_arree {τ1 τ2} :
      ⟨ Γ ⊢ τ1 ∷ kstar ⟩  →
      ⟨ Γ ⊢ τ2 ∷ kstar ⟩  →
      ⟨ Γ ⊢ arree τ1 τ2 ∷ kstar ⟩
  | K_arrτe {τ k} :
      ⟨ Γ ► k ⊢ τ ∷ kstar ⟩  →
      ⟨ Γ ⊢ arrτe k τ ∷ kstar ⟩
  | K_arrγe {τ1 τ2 τ3 k} :
      ⟨ Γ ◅ τ1 ~ τ2 ∷ k ⊢ τ3 ∷ kstar ⟩  →
      ⟨ Γ ⊢ arrγe τ1 τ2 k τ3 ∷ kstar ⟩
where "⟨ Γ ⊢ τ ∷ k ⟩" := (OfKind Γ τ k).

Reserved Notation "⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ k ⟩"
  ( at level 0,
    Γ at level 98,
    γ at level 98,
    τ1 at level 98,
    τ2 at level 98,
    k at level 98).

Inductive OfProp (Γ: Env) : Tm → Tm → Tm → Kind → Prop :=
  | R_τvar {α k} :
      ⟨ α ∷ k ∈ Γ ⟩ →
      ⟨ Γ ⊢ var α : var α ~ var α ∷ k ⟩
  | R_cvar {c τ1 τ2 k} :
      ⟨ c : τ1 ~ τ2 ∷ k ∈ Γ ⟩ →
      ⟨ Γ ⊢ var c : τ1 ~ τ2 ∷ k ⟩
  | R_γabsττ {γ τ1 τ2 k1 k2} :
      ⟨ Γ ► k1 ⊢ γ : τ1 ~ τ2 ∷ k2 ⟩ →
      ⟨ Γ ⊢ γabsττ k1 γ : absττ k1 τ1 ~ absττ k1 τ2 ∷ karr k1 k2 ⟩
  | R_γappττ {γ1 γ2 τ11 τ12 τ21 τ22 k1 k2 }:
      ⟨ Γ ⊢ γ1 : τ11 ~ τ21 ∷ karr k1 k2 ⟩ →
      ⟨ Γ ⊢ γ2 : τ12 ~ τ22 ∷ k1 ⟩ →
      ⟨ Γ ⊢ γappττ γ1 γ2 : appττ τ11 τ12 ~ appττ τ21 τ22 ∷ k2 ⟩
  | R_γarree {γ1 γ2 τ11 τ12 τ21 τ22}:
      ⟨ Γ ⊢ γ1 : τ11 ~ τ21 ∷ kstar ⟩ →
      ⟨ Γ ⊢ γ2 : τ12 ~ τ22 ∷ kstar ⟩ →
      ⟨ Γ ⊢ γarree γ1 γ2 : arree τ11 τ21 ~ arree τ21 τ22 ∷ kstar ⟩
  | R_γarrτe {γ τ1 τ2 k} :
      ⟨ Γ ► k ⊢ γ : τ1 ~ τ2 ∷ kstar ⟩ →
      ⟨ Γ ⊢ γarrτe k γ : arrτe k τ1 ~ arrτe k τ2 ∷ kstar ⟩
  | R_γbeta {γ1 γ2 τ11 τ12 τ21 τ22 k1 k2} :
      ⟨ Γ ► k1 ⊢ γ1 : τ11 ~ τ21 ∷ k2 ⟩ →
      ⟨ Γ ⊢ γ2 : τ12 ~ τ22 ∷ k1 ⟩ →
      ⟨ Γ ⊢ γbeta γ1 γ2 : appττ (absττ k1 τ11) τ12 ~ τ21[beta1 τ22] ∷ k2 ⟩
  | R_γsym {γ τ1 τ2 k} :
      ⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ k ⟩ →
      ⟨ Γ ⊢ γsym γ : τ2 ~ τ1 ∷ k ⟩
  | R_γtrans {γ1 γ2 τ1 τ2 τ3 k} :
      ⟨ Γ ⊢ γ1 : τ1 ~ τ2 ∷ k ⟩ →
      ⟨ Γ ⊢ γ2 : τ2 ~ τ3 ∷ k ⟩ →
      ⟨ Γ ⊢ γtrans γ1 γ2 : τ1 ~ τ3 ∷ k ⟩
where "⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ k ⟩" := (OfProp Γ γ τ1 τ2 k).

Reserved Notation "⟨ Γ ⊢ e : τ ⟩"
  ( at level 0,
    Γ at level 98,
    e at level 98,
    τ at level 98).

Inductive OfType (Γ: Env) : Tm → Tm → Prop :=
  | T_evar {x τ} :
      ⟨ x : τ ∈ Γ ⟩ →
      ⟨ Γ ⊢ var x : τ ⟩
  | T_absee {e τ1 τ2} :
      ⟨ Γ ⊢ τ1 ∷ kstar ⟩ →
      ⟨ Γ ▻ τ1 ⊢ e : τ2 ⟩ →
      ⟨ Γ ⊢ absee τ1 e : arree τ1 τ2 ⟩
  | T_absτe {e τ k} :
      ⟨ Γ ► k ⊢ e : τ ⟩ →
      ⟨ Γ ⊢ absτe k e : arrτe k τ ⟩
  | T_absγe {e τ1 τ2 τ3 k} :
      ⟨ Γ ◅ τ1 ~ τ2 ∷ k ⊢ e : τ3 ⟩ →
      ⟨ Γ ⊢ absγe τ1 τ2 k e : arrγe τ1 τ2 k τ3 ⟩
  | T_appee {e1 e2 τ1 τ2} :
      ⟨ Γ ⊢ e1 : arree τ1 τ2 ⟩ →
      ⟨ Γ ⊢ e2 : τ1 ⟩ →
      ⟨ Γ ⊢ appee e1 e2 : τ2 ⟩
  | T_appeτ {e τ1 τ2 k} :
      ⟨ Γ ⊢ e : arrτe k τ1 ⟩ →
      ⟨ Γ ⊢ τ2 ∷ k ⟩ →
      ⟨ Γ ⊢ appeτ e τ2 : τ1[beta1 τ2] ⟩
  | T_appeγ {e γ τ1 τ2 τ3 k} :
      ⟨ Γ ⊢ e : arrγe τ1 τ2 k τ3 ⟩ →
      ⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ k ⟩ →
      ⟨ Γ ⊢ appeτ e γ : τ3 ⟩
  | T_cast {e γ τ1 τ2} :
      ⟨ Γ ⊢ e : τ1 ⟩ →
      ⟨ Γ ⊢ γ : τ1 ~ τ2 ∷ kstar ⟩ →
      ⟨ Γ ⊢ cast e γ : τ2 ⟩
where "⟨ Γ ⊢ e : τ ⟩" := (OfType Γ e τ).
