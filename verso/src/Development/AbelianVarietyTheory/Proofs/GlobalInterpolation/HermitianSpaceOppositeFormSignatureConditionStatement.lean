import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianSpaceOppositeFormSignatureCondition
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NegSpace.sigOK_neg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FHermitianSpaceOppositeFormSignatureCondition.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.hermitianSpaceOppositeForm_signatureCondition : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), W.SigOK → (GlobalTheory.NegSpace.neg W).SigOK := by
  first | exact @GlobalTheory.NegSpace.sigOK_neg | exact GlobalTheory.NegSpace.sigOK_neg | (intros; apply GlobalTheory.NegSpace.sigOK_neg <;> assumption)
