import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotMemForallGtEqMaximalIdeal
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPrimeNotMemForallGtEqMaximalIdeal.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_prime_not_mem_forall_gt_eq_maximalIdeal' : ∀ (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C] (x : C), x ≠ 0 → x ∈ maximalIdeal C → ∃ q : Ideal C, q.IsPrime ∧ x ∉ q ∧ ∀ P : Ideal C, P.IsPrime → q < P → P = maximalIdeal C := by
  first | exact @GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal | exact GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal | (intros; apply GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal <;> assumption)
