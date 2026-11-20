import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProduct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FRayLSeriesEulerProduct.lean&line=154#L154)
-/
theorem _root_.GlobalTheory.T.ray_L_series_euler_product : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ) (s : ℂ), 1 < s.re → LSeriesSummable (D.coef χ) s ∧ Summable (fun v : D.Pr => ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖) ∧ LSeries (D.coef χ) s = Complex.exp (∑' v : D.Pr, -Complex.log (1 - (χ (D.cls v.1.asIdeal) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  first | exact @GlobalTheory.Mem.RayData.lseries_eq_exp_tsum | exact GlobalTheory.Mem.RayData.lseries_eq_exp_tsum | (intros; apply GlobalTheory.Mem.RayData.lseries_eq_exp_tsum <;> assumption)
