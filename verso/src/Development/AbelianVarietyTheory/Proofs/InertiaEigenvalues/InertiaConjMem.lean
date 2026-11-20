import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

namespace GlobalTheory.InertiaConj

/- English proof (translation)
Rewrite using `[← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]`. Conclude with `(spectralNorm_eq_of_equiv τ x).symm`.
-/
theorem norm_aut_eq {l : ℕ} [Fact l.Prime] (τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (x : PadicAlgCl l) :
    ‖τ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv τ x).symm

/- English proof (translation)
Introduce `l _ g τ hg`. Establish `hS : ∀ σ : Gl l, (∀ x : Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1) → ∀ x : Om l, ‖x‖ ≤ 1 → ‖((τ⁻¹ * σ * τ : Gl l) : GQ l) x - x‖ < 1`. Introduce `σ hσ x hx`. Establish `hτx : ‖(τ : GQ l) x‖ ≤ 1` using `by rw [norm_aut_eq]; exact hx`. Establish `h1` using `hσ ((τ : GQ l) x) hτx`.

Establish `h2 : ((τ⁻¹ * σ * τ : Gl l) : GQ l) x - x = ((τ : GQ l).symm) ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x)`. Simplify using `[map_sub]`. Rewrite using `[h2, norm_aut_eq]`. Conclude with `h1`. Unfold `IK at hg ⊢`.

Proceed by induction on `hg using Subgroup.closure_induction with`. Consider the case `mem x hx => exact Subgroup.subset_closure (hS x hx)`. Consider the case `one => simp`. Consider the case `mul x y _ _ hx hy`. Establish `: τ⁻¹ * (x * y) * τ = (τ⁻¹ * x * τ) * (τ⁻¹ * y * τ)` using `by group`.

Rewrite using `[this]`. Conclude with `Subgroup.mul_mem _ hx hy`. Consider the case `inv x _ hx`. Establish `: τ⁻¹ * x⁻¹ * τ = (τ⁻¹ * x * τ)⁻¹` using `by group`. Rewrite using `[this]`.

Conclude with `Subgroup.inv_mem _ hx`.
-/
theorem inertia_conj_mem : ∀ (l : ℕ) [Fact l.Prime] (g τ : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) →
    τ⁻¹ * g * τ ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  intro l _ g τ hg
  have hS : ∀ σ : Gl l, (∀ x : Om l, ‖x‖ ≤ 1 → ‖(σ : GQ l) x - x‖ < 1) →
      ∀ x : Om l, ‖x‖ ≤ 1 → ‖((τ⁻¹ * σ * τ : Gl l) : GQ l) x - x‖ < 1 := by
    intro σ hσ x hx
    have hτx : ‖(τ : GQ l) x‖ ≤ 1 := by rw [norm_aut_eq]; exact hx
    have h1 := hσ ((τ : GQ l) x) hτx
    have h2 : ((τ⁻¹ * σ * τ : Gl l) : GQ l) x - x =
        ((τ : GQ l).symm) ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) := by
      simp [map_sub]
    rw [h2, norm_aut_eq]
    exact h1
  unfold IK at hg ⊢
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hS x hx)
  | one => simp
  | mul x y _ _ hx hy =>
    have : τ⁻¹ * (x * y) * τ = (τ⁻¹ * x * τ) * (τ⁻¹ * y * τ) := by group
    rw [this]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have : τ⁻¹ * x⁻¹ * τ = (τ⁻¹ * x * τ)⁻¹ := by group
    rw [this]; exact Subgroup.inv_mem _ hx

end GlobalTheory.InertiaConj
