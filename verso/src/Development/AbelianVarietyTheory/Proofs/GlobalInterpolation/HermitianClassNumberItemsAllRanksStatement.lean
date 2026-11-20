import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianClassNumberItemsAllRanks
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FHermitianClassNumberItemsAllRanks.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.hermitianClassNumberItems_all_ranks : ∀ (D : D7) (n : ℕ), ClassItemsAt D n := by
  first | exact @GlobalTheory.classItemsAt_all | exact GlobalTheory.classItemsAt_all | (intros; apply GlobalTheory.classItemsAt_all <;> assumption)
