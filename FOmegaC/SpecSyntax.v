Require Export ParDB.Spec.

Implicit Types x y α β c : Ix.

Inductive Kind : Type :=
  | kstar
  | karr (k1 k2 : Kind).

Implicit Types k : Kind.

Inductive Tm : Type :=
  | var    x
  (**********************)
  | absee  (τ e: Tm)
  | absτe  k (e: Tm)
  | absγe  (τ1 τ2 e : Tm)
  | appee  (e1 e2 : Tm)
  | appeτ  (e τ: Tm)
  | appeγ  (e γ: Tm)
  | cast   (e γ: Tm)
  (**********************)
  | absττ  k (τ: Tm)
  | appττ  (τ1 τ2: Tm)
  | arree  (τ1 τ2: Tm)
  | arrτe  k (τ: Tm)
  | arrγe  (τ1 τ2 τ3: Tm)
  (**********************)
  | γabsττ k (γ: Tm)
  | γappττ (γ1 γ2: Tm)
  | γarree (γ1 γ2: Tm)
  | γarrτe k (γ: Tm)
  | γarrγe (τ1 τ2 γ: Tm)
  | γsym   (γ: Tm)
  | γtrans (γ1 γ2: Tm).

Implicit Types t e τ γ : Tm.

Inductive Env : Set :=
  | nil
  | evar (Γ: Env) τ
  | τvar (Γ: Env) k
  | γvar (Γ: Env) τ τ.

Notation "Γ ▻ τ"       := (evar Γ τ) (at level 55, left associativity).
Notation "Γ ► k"       := (τvar Γ k) (at level 55, left associativity).
Notation "Γ ◅ τ1 ~ τ2" := (γvar Γ τ1 τ2) (at level 55, left associativity).

Section DeBruijn.

  Context {X: Type}.
  Context {vrX: Vr X}.
  Context {wkX: Wk X}.
  Context {vrTm: Vr Tm}.
  Context {liftXTm: Lift X Tm}.

  Fixpoint apTm (ζ: Sub X) (t: Tm) {struct t} : Tm :=
    match t with
      | var x          => lift (ζ x)
      (**************************************************************)
      | absee τ e      => absee (apTm ζ τ) (apTm ζ↑ e)
      | absτe k e      => absτe k (apTm ζ↑ e)
      | absγe τ1 τ2 e  => absγe (apTm ζ τ1) (apTm ζ τ2) (apTm ζ↑ e)
      | appee e1 e2    => appee (apTm ζ e1) (apTm ζ e2)
      | appeτ e τ      => appeτ (apTm ζ e) (apTm ζ τ)
      | appeγ e γ      => appeγ (apTm ζ e) (apTm ζ γ)
      | cast e γ       => cast (apTm ζ e) (apTm ζ γ)
      (**************************************************************)
      | absττ k τ      => absττ k (apTm ζ↑ τ)
      | appττ τ1 τ2    => appττ (apTm ζ τ1) (apTm ζ τ2)
      | arree τ1 τ2    => arree (apTm ζ τ1) (apTm ζ↑ τ2)
      | arrτe k τ      => arrτe k (apTm ζ↑ τ)
      | arrγe τ1 τ2 τ3 => arrγe (apTm ζ τ1) (apTm ζ τ2) (apTm ζ τ3)
      (**************************************************************)
      | γabsττ k γ     => γabsττ k (apTm ζ↑ γ)
      | γappττ γ1 γ2   => γappττ (apTm ζ γ1) (apTm ζ γ2)
      | γarree γ1 γ2   => γarree (apTm ζ γ1) (apTm ζ γ2)
      | γarrτe k γ     => γarrτe k (apTm ζ↑ γ)
      | γarrγe τ1 τ2 γ => γarrγe (apTm ζ τ1) (apTm ζ τ2) (apTm ζ γ)
      | γsym γ         => γsym (apTm ζ γ)
      | γtrans γ1 γ2   => γtrans (apTm ζ γ1) (apTm ζ γ2)
    end.

End DeBruijn.
