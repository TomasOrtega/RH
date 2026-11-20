import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremWachModuleLemmaHypothesesAdmitted
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLiftingTheoremWachModuleLemmaHypothesesAdmitted.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.liftingTheorem_wachModuleLemma_hypotheses_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LiftingTheory.admitted D HW F Cm ∧ CrystallineLiftingBounds.admitted D HW F Cm := by
  first | exact @GlobalTheory.LiftAdmitted.all_admitted | exact GlobalTheory.LiftAdmitted.all_admitted | (intros; apply GlobalTheory.LiftAdmitted.all_admitted <;> assumption)
