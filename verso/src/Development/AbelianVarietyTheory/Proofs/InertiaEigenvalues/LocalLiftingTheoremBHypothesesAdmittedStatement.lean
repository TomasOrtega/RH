import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBHypothesesAdmitted
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLocalLiftingTheoremBHypothesesAdmitted.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.localLifting_theoremB_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ArcLiftingSetup.admitted D HW F Cm 10 23 32 32 8 := by
  first | exact @GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum | exact GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum | (intros; apply GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum <;> assumption)
