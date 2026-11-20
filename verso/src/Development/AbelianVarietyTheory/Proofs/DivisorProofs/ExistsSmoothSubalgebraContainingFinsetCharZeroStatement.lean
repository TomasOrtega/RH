import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSubalgebraContainingFinsetCharZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsSmoothSubalgebraContainingFinsetCharZero.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_smooth_subalgebra_containing_finset_charZero : ∀ (F K : Type) [Field F] [CharZero F] [Field K] [Algebra F K] (s : Finset K), ∃ R : Subalgebra F K, (↑s : Set K) ⊆ (R : Set K) ∧ Algebra.Smooth F R := by
  first | exact @GlobalTheory.exists_smooth_subalgebra_of_finset | exact GlobalTheory.exists_smooth_subalgebra_of_finset | (intros; apply GlobalTheory.exists_smooth_subalgebra_of_finset <;> assumption)
