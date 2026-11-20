import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerTubeGaugeMassAsymptotic
import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushCut
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FStabilizerTubeGaugeMassAsymptotic.lean&line=457#L457)
-/
theorem _root_.GlobalTheory.T.stabilizerTube_gaugeMass_asymptotic : PI.RhsWLim.W.TubeLimK := by
  first | exact @GlobalTheory.StabTube.tubeLimK | exact GlobalTheory.StabTube.tubeLimK | (intros; apply GlobalTheory.StabTube.tubeLimK <;> assumption)
