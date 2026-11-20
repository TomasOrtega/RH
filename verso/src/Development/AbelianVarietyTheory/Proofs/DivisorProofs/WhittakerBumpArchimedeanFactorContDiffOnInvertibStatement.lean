import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerBumpArchimedeanFactorContDiffOnInvertib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperDiagEqSdM
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FWhittakerBumpArchimedeanFactorContDiffOnInvertib.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.whittakerBumpArchimedeanFactor_contDiffOn_invertible : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (f : Lie E n → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ invSet E n → ContDiffOn ℝ ∞ (bumpInf f) (invSet E n) := by
  first | exact @GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet | exact GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet | (intros; apply GlobalTheory.WhitBump.bumpInf_contDiffOn_invSet <;> assumption)
