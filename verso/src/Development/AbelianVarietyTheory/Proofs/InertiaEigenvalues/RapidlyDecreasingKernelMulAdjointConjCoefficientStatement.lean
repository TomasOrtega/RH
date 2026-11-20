import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RapidlyDecreasingKernelMulAdjointConjCoefficient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JSW.isRapidInf_mul_adCoef` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FRapidlyDecreasingKernelMulAdjointConjCoefficient.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.rapidlyDecreasingKernel_mul_adjointConjCoefficient : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ →
      ∀ p, IsRapidInf ν (fun x => k x * adCoef (γ x) p) γ := by
  first | exact @GlobalTheory.JSW.isRapidInf_mul_adCoef | exact GlobalTheory.JSW.isRapidInf_mul_adCoef | (intros; apply GlobalTheory.JSW.isRapidInf_mul_adCoef <;> assumption)
