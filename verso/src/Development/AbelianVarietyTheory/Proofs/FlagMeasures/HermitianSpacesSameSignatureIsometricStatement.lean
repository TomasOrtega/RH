import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometric
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHermitianSpacesSameSignatureIsometric.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.hermitian_spaces_same_signature_isometric : SameKindIsometric := by
  first | exact @GlobalTheory.FlagMeas.sameKindIsometric | exact GlobalTheory.FlagMeas.sameKindIsometric | (intros; apply GlobalTheory.FlagMeas.sameKindIsometric <;> assumption)
