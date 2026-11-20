import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodBoundAllConstantGeForty
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfLiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertiaEigenvalues.theoremT_all_records` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FCrystallinePeriodBoundAllConstantGeForty.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.crystallinePeriodBound_all_constant_ge_forty : GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.FontaineBcris → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℕ, 40 ≤ C → ElementDenominator.Conclusion2 D C := by
  first | exact @GlobalTheory.InertiaEigenvalues.theoremT_all_records | exact GlobalTheory.InertiaEigenvalues.theoremT_all_records | (intros; apply GlobalTheory.InertiaEigenvalues.theoremT_all_records <;> assumption)
