import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisSectionTupleQuotients
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MvPolynomial GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTranscendenceBasisSectionTupleQuotients.lean&line=35#L35)
-/
theorem _root_.GlobalTheory.T.transcendenceBasis_sectionTupleQuotients : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K) (l : Fin (D + 1)) (A : Subring K), Algebra.trdeg ℤ K = D → x l ≠ 0 → Algebra.FiniteType ℤ A → (∀ w ∈ A, IsIntegral (ratR x l) w) → (∀ w : K, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ w = a / b) → (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧ FiniteDimensional (ratF x) K := by
  first | exact @GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR | exact GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR | (intros; apply GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR <;> assumption)
