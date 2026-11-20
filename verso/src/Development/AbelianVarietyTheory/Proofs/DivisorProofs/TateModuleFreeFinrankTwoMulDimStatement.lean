import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AV.AbVar.tl_free_finrank` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTateModuleFreeFinrankTwoMulDim.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.tateModule_free_finrank_two_mul_dim : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K), Module.Free ℤ_[l] (Tl l A) ∧ Module.Finite ℤ_[l] (Tl l A) ∧ Module.finrank ℤ_[l] (Tl l A) = 2 * A.dim ∧ Module.Finite ℚ_[l] (Vl l A) ∧ Module.finrank ℚ_[l] (Vl l A) = 2 * A.dim := by
  first | exact @GlobalTheory.AV.AbVar.tl_free_finrank | exact GlobalTheory.AV.AbVar.tl_free_finrank | (intros; apply GlobalTheory.AV.AbVar.tl_free_finrank <;> assumption)
