import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroCommonZeroOfIsHomogeneous
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_ne_zero_common_zero_of_isHomogeneous` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsNeZeroCommonZeroOfIsHomogeneous.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_ne_zero_common_zero_of_isHomogeneous' : ∀ (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ) (f : Fin r → MvPolynomial (Fin n) k), (∀ i, ∃ d, 0 < d ∧ (f i).IsHomogeneous d) → r < n → ∃ x : Fin n → k, x ≠ 0 ∧ ∀ i, MvPolynomial.eval x (f i) = 0 := by
  first | exact @GlobalTheory.exists_ne_zero_common_zero_of_isHomogeneous | exact GlobalTheory.exists_ne_zero_common_zero_of_isHomogeneous | (intros; apply GlobalTheory.exists_ne_zero_common_zero_of_isHomogeneous <;> assumption)
