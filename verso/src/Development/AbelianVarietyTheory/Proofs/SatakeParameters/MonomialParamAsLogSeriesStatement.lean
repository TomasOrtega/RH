import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonomialParamAsLogSeries
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FMonomialParamAsLogSeries.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.exists_inParam_eq_monomial_low_coeff_zero : ∀ (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (n : ι →₀ ℕ), ∃ U : MvPowerSeries ι (K0 p), inParam p U = MvPowerSeries.monomial n 1 ∧ (∀ m : ι →₀ ℕ, m.degree < n.degree → MvPowerSeries.coeff m U = 0) := by
  first | exact @GlobalTheory.TwU.monomial_param_as_log_series | exact GlobalTheory.TwU.monomial_param_as_log_series | (intros; apply GlobalTheory.TwU.monomial_param_as_log_series <;> assumption)
