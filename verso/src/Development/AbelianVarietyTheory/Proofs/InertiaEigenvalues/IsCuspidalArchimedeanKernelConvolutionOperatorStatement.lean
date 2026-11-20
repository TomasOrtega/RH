import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCuspidalArchimedeanKernelConvolutionOperator
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsCuspidalArchimedeanKernelConvolutionOperator.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.isCuspidal_archimedeanKernelConvolutionOperator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : Type) [MeasurableSpace X] (ν : Measure X)
    [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)), IsRapidInf ν k γ → ∀ φ : Sm E a, IsBCC φ.1 →
      IsCuspidal (kerOp ν k γ φ.1) := by
  first | exact @GlobalTheory.JSW.isCuspidal_kerOp | exact GlobalTheory.JSW.isCuspidal_kerOp | (intros; apply GlobalTheory.JSW.isCuspidal_kerOp <;> assumption)
