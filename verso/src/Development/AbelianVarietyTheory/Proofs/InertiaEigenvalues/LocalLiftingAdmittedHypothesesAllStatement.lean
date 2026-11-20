import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingAdmittedHypothesesAll
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfLiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.UsedConclusionOfUsedInputs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLocalLiftingAdmittedHypothesesAll.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.localLifting_admittedHypotheses_all : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ElementDenominator.Adm2 D HW F := by
  first | exact @GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt | exact GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt | (intros; apply GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt <;> assumption)
