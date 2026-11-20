import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NomePowerSeriesDvdOfSumBounded
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FNomePowerSeriesDvdOfSumBounded.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.nomePowerSeries_dvd_of_sum_bounded : ∀ (G H : PowerSeries ℂ) (T C : ℝ) (g h : ℂ → ℂ), H ≠ 0 → (∀ w : ℂ, T < w.im → SumsAt G w (g w) ∧ SumsAt H w (h w) ∧ (h w ≠ 0 → ‖g w‖ ≤ C * ‖h w‖)) → H ∣ G := by
  first | exact @GlobalTheory.powerSeries_dvd_of_sum_bounded | exact GlobalTheory.powerSeries_dvd_of_sum_bounded | (intros; apply GlobalTheory.powerSeries_dvd_of_sum_bounded <;> assumption)
