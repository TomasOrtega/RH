import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowShareRequirementClosedFormProof
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EX.G4.wClosed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FWindowShareRequirementClosedFormProof.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.windowShareRequirementClosedForm_proof : DC.WClosed := by
  first | exact @GlobalTheory.EX.G4.wClosed | exact GlobalTheory.EX.G4.wClosed | (intros; apply GlobalTheory.EX.G4.wClosed <;> assumption)
