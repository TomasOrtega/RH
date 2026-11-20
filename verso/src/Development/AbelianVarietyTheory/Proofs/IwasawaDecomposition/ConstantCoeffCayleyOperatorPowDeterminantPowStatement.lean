import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantCoeffCayleyOperatorPowDeterminantPow
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FConstantCoeffCayleyOperatorPowDeterminantPow.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.constantCoeff_cayleyOperator_pow_determinant_pow : ∀ (p q : ℕ), constantCoeff ((cayOp p ℂ ^ q) (cayDet p ℂ ^ q)) = ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  first | exact @GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow | exact GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow | (intros; apply GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow <;> assumption)
