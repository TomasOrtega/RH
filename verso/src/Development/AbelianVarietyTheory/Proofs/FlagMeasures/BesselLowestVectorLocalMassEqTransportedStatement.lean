import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselLowestVectorLocalMassEqTransported
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FBesselLowestVectorLocalMassEqTransported.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.l2SG_phiOf_eq_l2SG_wT_of_goodLoc : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB → ∀ (u : D.what₂.Word) (τ : D.what₂.Tau), l2SG (C.nuS u τ) (phiOf hB u τ) = l2SG (C.nuS u τ) (wT C u τ) := by
  first | exact @GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported | exact GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported | (intros; apply GlobalTheory.PhiTranslate.bessel_lowest_vector_local_mass_eq_transported <;> assumption)
