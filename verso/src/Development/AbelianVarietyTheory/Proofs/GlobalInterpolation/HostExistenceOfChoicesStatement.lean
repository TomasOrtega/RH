import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostExistenceOfChoices
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EX.HostExist.hostEx` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FHostExistenceOfChoices.lean&line=308#L308)
-/
theorem _root_.GlobalTheory.T.host_existence_of_choices : QDChoice → ThinChoice → NormPrimes → SmallPrimeOne → TopsChoice → HostEx := by
  first | exact @GlobalTheory.EX.HostExist.hostEx | exact GlobalTheory.EX.HostExist.hostEx | (intros; apply GlobalTheory.EX.HostExist.hostEx <;> assumption)
