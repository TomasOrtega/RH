import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitIndicatorsMatchAtOfOneLtNormFirstMoment
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullToGlIsSelfAdjoint
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FUnitIndicatorsMatchAtOfOneLtNormFirstMoment.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.unitIndicators_matchAt_of_one_lt_norm_firstMoment : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas (r + 1) F E) (a : Inv (r + 1) F), 1 < ‖a.2.1 0‖ → MatchAt M (unitG (r + 1) F) (unitU (r + 1) F E) a := by
  first | exact @GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm | exact GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm | (intros; apply GlobalTheory.JR.BigMoment.matchAt_unit_of_one_lt_norm <;> assumption)
