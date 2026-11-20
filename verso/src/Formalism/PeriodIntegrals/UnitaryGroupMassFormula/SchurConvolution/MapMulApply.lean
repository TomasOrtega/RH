import Mathlib
import Formalism.PeriodIntegrals.PhSchurConv

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PI.UnitaryGroupMassFormula.PhSchurConv.Main

open PI.PhSchurConv

/- English proof (translation)
Conclude with `inner_conj_symm b a`.
-/
theorem star_inner {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (a b : H) :
    star ⟪a, b⟫_ℂ = ⟪b, a⟫_ℂ := by
  exact inner_conj_symm b a

/- English proof (translation)
Rewrite using `[hU.2.1 a b]`. Both sides reduce to the same expression.
-/
theorem map_mul_apply {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (a b : G) (v : H) : σ (a * b) v = σ a (σ b v) := by
  rw [hU.2.1 a b]
  rfl

/- English proof (translation)
Set `L : H →ₗᵢ[ℂ] H` to `⟨(σ g).toLinearMap, hU.2.2.1 g⟩`. Conclude with `L.inner_map_map a b`.
-/
theorem inner_map {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g : G) (a b : H) : ⟪σ g a, σ g b⟫_ℂ = ⟪a, b⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(σ g).toLinearMap, hU.2.2.1 g⟩
  exact L.inner_map_map a b

/- English proof (translation)
Rewrite using `[star_inner, ← inner_map hU g w (σ g⁻¹ w), ← map_mul_apply hU, mul_inv_cancel, hU.1, ContinuousLinearMap.one_apply]`.
-/
theorem coef_inv {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g : G) (w : H) :
    ⟪w, σ g⁻¹ w⟫_ℂ = star ⟪w, σ g w⟫_ℂ := by
  rw [star_inner, ← inner_map hU g w (σ g⁻¹ w), ← map_mul_apply hU, mul_inv_cancel, hU.1,
    ContinuousLinearMap.one_apply]

/- English proof (translation)
Establish `h1 : σ g (σ x w) = σ (g * x) w` using `(map_mul_apply hU g x w).symm`. Rewrite using `[h1]`. Use `symm`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← map_mul_apply hU, ← map_mul_apply hU, inv_mul_cancel, hU.1, ContinuousLinearMap.one_apply, mul_inv_rev]`.
-/
theorem coef_conv {G : Type} [Group G] [TopologicalSpace G]
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : G → (H →L[ℂ] H)} (hU : IsURep σ) (g x y : G) (w : H) :
    ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ = ⟪σ g (σ x w), σ y w⟫_ℂ := by
  have h1 : σ g (σ x w) = σ (g * x) w := (map_mul_apply hU g x w).symm
  rw [h1]
  symm
  calc ⟪σ (g * x) w, σ y w⟫_ℂ = ⟪σ (g * x)⁻¹ (σ (g * x) w), σ (g * x)⁻¹ (σ y w)⟫_ℂ := (inner_map hU _ _ _).symm
    _ = ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ := by
      rw [← map_mul_apply hU, ← map_mul_apply hU, inv_mul_cancel, hU.1, ContinuousLinearMap.one_apply,
        mul_inv_rev]

end PI.UnitaryGroupMassFormula.PhSchurConv.Main
