import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelGaussianPairStandardGaussian
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.siegelGauss_pair_standard` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSiegelGaussianPairStandardGaussian.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.siegelGaussian_pair_standardGaussian : ∀ (l : Type) [Fintype l] [DecidableEq l] (τ : Matrix l l ℂ) (c : ℂ), GlobalTheory.IsSiegel τ → (∫ x : l → ℝ, c * cexp (π * I * ((fun i => (x i : ℂ)) ⬝ᵥ τ *ᵥ fun i => (x i : ℂ))) * conj (cexp (-π * ((x ⬝ᵥ x : ℝ) : ℂ)))) ^ 2 * (1 - I • τ).det = c ^ 2 := by
  first | exact @GlobalTheory.siegelGauss_pair_standard | exact GlobalTheory.siegelGauss_pair_standard | (intros; apply GlobalTheory.siegelGauss_pair_standard <;> assumption)
