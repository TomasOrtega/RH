import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem simpleU_rev_and_sq : ∀ (n : ℕ) (k : Fin (n / 2)), (∀ i, simpleU k i.rev = (simpleU k i).rev) ∧ simpleU k * simpleU k = 1 := by
  intro n k
  have hk := k.isLt
  have hn : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  unfold simpleU partnerU
  split_ifs with h
  · refine ⟨fun i => ?_, ?_⟩
    · have hi := i.isLt
      simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]
      split_ifs at * <;> simp only [Fin.ext_iff, Fin.val_rev, lo, Fin.coe_castLE] at * <;> omega
    · have hnd : [lo k, lo (⟨k.val + 1, h⟩ : Fin (n / 2)), (lo k).rev,
          (lo (⟨k.val + 1, h⟩ : Fin (n / 2))).rev].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
          and_true, Fin.ext_iff, Fin.val_rev, lo, Fin.coe_castLE, not_false_eq_true]
        omega
      have hc := (Equiv.Perm.disjoint_swap_swap hnd).commute
      rw [hc.symm.mul_mul_mul_comm, Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  · refine ⟨fun i => ?_, Equiv.swap_mul_self _ _⟩
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, lo] <;> omega

end GlobalTheory
