import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianVolumeDependsOnlyOnFieldSignature
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHermitianVolumeDependsOnlyOnFieldSignature.lean&line=175#L175)
-/
theorem _root_.GlobalTheory.T.hermitian_volume_depends_only_on_field_signature : VolumeInvariant := by
  first | exact @GlobalTheory.VolInvariant.volumeInvariant | exact GlobalTheory.VolInvariant.volumeInvariant | (intros; apply GlobalTheory.VolInvariant.volumeInvariant <;> assumption)
