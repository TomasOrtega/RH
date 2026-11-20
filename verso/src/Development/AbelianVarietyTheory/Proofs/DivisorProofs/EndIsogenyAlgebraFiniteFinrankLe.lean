import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDimStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `K _ A`. Take `⟨hfin, hfree, hrk⟩` from `GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim K A A`. Use `haveI : Module.Finite ℤ (End A) := hfin`. Use `haveI : Module.Free ℤ (End A) := hfree`. Use `⟨inferInstance, ?_⟩` and prove the remaining obligations.

Rewrite using `[Module.finrank_baseChange]`. Conclude with `hrk`.
-/
theorem end_isogeny_algebra_finrank_le : ∀ (K : Type) [Field K] (A : AbVar K),
    Module.Finite ℚ (End0 A) ∧ Module.finrank ℚ (End0 A) ≤ 4 * A.dim * A.dim := by
  intro K _ A
  obtain ⟨hfin, hfree, hrk⟩ := GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim K A A
  haveI : Module.Finite ℤ (End A) := hfin
  haveI : Module.Free ℤ (End A) := hfree
  refine ⟨inferInstance, ?_⟩
  rw [Module.finrank_baseChange]
  exact hrk

end GlobalTheory.AV.AbVar
