import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremCConst25OfHypotheses
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
import Formalism.SharpRestriction.LevelLetterCocycles.LetterConditionGlobal
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.theoremC_of_admitted_inputs` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTheoremCConst25OfHypotheses.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.ramified_coefficient_chains_of_hypotheses : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (CR CA CB CK : ℝ), LiftingTheory.adm23 D HW F → Formalism.MainNotions.N.LetterConditionGlobal D HW F → ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F → CrystallineLiftingBounds.adm22 D HW F → InvariantsGenerators.LitFont D HW F → RamifiedCoefficientChains.Stmt D HW F Cm 25 CR CA CB CK := by
  first | exact @GlobalTheory.theoremC_of_admitted_inputs | exact GlobalTheory.theoremC_of_admitted_inputs | (intros; apply GlobalTheory.theoremC_of_admitted_inputs <;> assumption)
