import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamifiedCoefficientChainsPrvTwentyFive
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FRamifiedCoefficientChainsPrvTwentyFive.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.prv_twenty_five_of_blochKato_tateDuality_eulerChar : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), RamifiedCoefficientChains.aux₃ D HW F 25 := by
  first | exact @GlobalTheory.ramifiedCoefficientChains_prv_twenty_five | exact GlobalTheory.ramifiedCoefficientChains_prv_twenty_five | (intros; apply GlobalTheory.ramifiedCoefficientChains_prv_twenty_five <;> assumption)
