import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremEHypothesesAdmitted
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdmThmE.admitted_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLocalLiftingTheoremEHypothesesAdmitted.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.localLifting_theoremE_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), WachCoordinates.admitted D HW F Cm 10 := by
  first | exact @GlobalTheory.AdmThmE.admitted_all | exact GlobalTheory.AdmThmE.admitted_all | (intros; apply GlobalTheory.AdmThmE.admitted_all <;> assumption)
