import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSiegelUpperHalfSpaceNegMulInvSymplectic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsEqTransposeMulDiagonalMul
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsSiegelUpperHalfSpaceNegMulInvSymplectic.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.isSiegelUpperHalfSpace_neg_mul_inv_symplectic : ∀ (l : Type) [Fintype l] [DecidableEq l] (s : Matrix (l ⊕ l) (l ⊕ l) ℝ) (P Q : Matrix l l ℂ), (∀ a b, P a b = (s (.inl a) (.inl b) : ℂ) - I * (s (.inl a) (.inr b) : ℂ)) → (∀ a b, Q a b = (s (.inr a) (.inl b) : ℂ) - I * (s (.inr a) (.inr b) : ℂ)) → s ∈ Matrix.symplecticGroup l ℝ → P.det ≠ 0 → (-(Q * P⁻¹)).IsSymm → GlobalTheory.IsSiegel (-(Q * P⁻¹)) := by
  first | exact @GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic | exact GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic | (intros; apply GlobalTheory.IsSiegel.neg_mul_inv_of_symplectic <;> assumption)
