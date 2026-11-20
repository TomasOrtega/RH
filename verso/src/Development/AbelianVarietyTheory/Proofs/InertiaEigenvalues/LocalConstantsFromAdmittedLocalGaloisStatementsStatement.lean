import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FLocalConstantsFromAdmittedLocalGaloisStatements.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.localConstants_from_admitted_local_Galois_statements : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LiftingTheory.aux₃ D HW F 10 23 32 32 := by
  first | exact @GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt | exact GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt | (intros; apply GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt <;> assumption)
