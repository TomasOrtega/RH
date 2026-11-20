import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalPrimeCharNotMemFiniteTypeInt
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMaximalPrimeCharNotMemFiniteTypeInt.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.exists_maximal_prime_char_not_mem_finiteType_int : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (f : R), f ≠ 0 → ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ M := by
  first | exact @GlobalTheory.closedPt_of_finiteType_int | exact GlobalTheory.closedPt_of_finiteType_int | (intros; apply GlobalTheory.closedPt_of_finiteType_int <;> assumption)
