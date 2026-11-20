import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfLocalFilteredHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTheoremBOfLocalFilteredHypotheses.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.theoremB_of_localFilteredHypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (C CR CA CB CK Ckap : ℝ), (320 : ℝ) ≤ C → CrystallineLiftingBounds.adm22 D HW F → CrystallineLiftingBounds.adm23 D HW F → Formalism.MainNotions.N.LetterConditionGlobal D HW F → ArcLiftingSetup.Stmt D HW F Cm C CR CA CB CK Ckap := by
  first | exact @GlobalTheory.theoremB_of_admitted_inputs | exact GlobalTheory.theoremB_of_admitted_inputs | (intros; apply GlobalTheory.theoremB_of_admitted_inputs <;> assumption)
