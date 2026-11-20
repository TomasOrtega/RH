import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermInvariantOfConsSwapAndTail
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.perm_invariant_of_cons_swap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPermInvariantOfConsSwapAndTail.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.perm_invariant_of_cons_swap_and_tail : ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by
  first | exact @GlobalTheory.perm_invariant_of_cons_swap | exact GlobalTheory.perm_invariant_of_cons_swap | (intros; apply GlobalTheory.perm_invariant_of_cons_swap <;> assumption)
