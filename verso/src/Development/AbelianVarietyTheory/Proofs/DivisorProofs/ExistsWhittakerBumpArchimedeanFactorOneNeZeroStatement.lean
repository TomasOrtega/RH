import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerBumpArchimedeanFactorOneNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsWhittakerBumpArchimedeanFactorOneNeZero.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.exists_whittakerBumpArchimedeanFactor_one_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), ∃ f : Lie E n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ invSet E n ∧ bumpInf f (oneL E n) ≠ 0 := by
  first | exact @GlobalTheory.WhitBump.exists_bumpInf_oneL_ne_zero | exact GlobalTheory.WhitBump.exists_bumpInf_oneL_ne_zero | (intros; apply GlobalTheory.WhitBump.exists_bumpInf_oneL_ne_zero <;> assumption)
