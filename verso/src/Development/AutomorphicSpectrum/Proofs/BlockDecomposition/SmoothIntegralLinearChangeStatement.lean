import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChange
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Rodier.SmIntHaar.smInt_comp_inv_mulVec` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSmoothIntegralLinearChange.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.smooth_integral_linear_change : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (t : ℕ) [MeasurableSpace (Fin t → k)] [BorelSpace (Fin t → k)] (μ : MeasureTheory.Measure (Fin t → k)) [μ.IsAddHaarMeasure] {Z : Type} [AddCommGroup Z] [Module ℂ Z] (w : GL (Fin t) k) (φ : (Fin t → k) → Z), IsLocallyConstant φ → HasCompactSupport φ → smInt μ (fun v => φ (((w⁻¹ : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v)) = ((detChar (Fin t) (absPow k (1 : ℂ)) w : ℂˣ) : ℂ) • smInt μ φ := by
  first | exact @GlobalTheory.CompanionTheory.Rodier.SmIntHaar.smInt_comp_inv_mulVec | exact GlobalTheory.CompanionTheory.Rodier.SmIntHaar.smInt_comp_inv_mulVec | (intros; apply GlobalTheory.CompanionTheory.Rodier.SmIntHaar.smInt_comp_inv_mulVec <;> assumption)
