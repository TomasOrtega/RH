import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FExistsAdelesHaarMeasureCovolumeOne.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_measure_isCov1 : ∀ (F : Type) [Field F] [NumberField F], ∃ ν : Measure (AF F), IsCov1 ν := by
  first | exact @GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one | exact GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one | (intros; apply GlobalTheory.SWQ.exists_adeles_haarMeasure_covolume_one <;> assumption)
