import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

namespace GlobalTheory

/- English proof (translation)
Introduce `n k`. Establish `hk` using `k.isLt`. Establish `hn : 2 * (n / 2) ≤ n` using `Nat.mul_div_le n 2`. Unfold `simpleU partnerU`. Use `split_ifs with h`.

Use `⟨fun i => ?_, ?_⟩` and prove the remaining obligations. Establish `hi` using `i.isLt`. Simplify using `only [Equiv.Perm.mul_apply, Equiv.swap_apply_def]`. Apply the tactic sequence `split_ifs at * <;> simp only [Fin.ext_iff, Fin.val_rev, lo, Fin.coe_castLE] at * <;> omega`. Establish `hnd : [lo k, lo (⟨k.val + 1, h⟩ : Fin (n / 2)), (lo k).rev, (lo (⟨k.val + 1, h⟩ : Fin (n / 2))).rev].Nodup`.

Simplify using `only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil, and_true, Fin.ext_iff, Fin.val_rev, lo, Fin.coe_castLE, not_false_eq_true]`. Use linear arithmetic over natural numbers and integers. Establish `hc` using `(Equiv.Perm.disjoint_swap_swap hnd).commute`. Rewrite using `[hc.symm.mul_mul_mul_comm, Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]`. Use `⟨fun i => ?_, Equiv.swap_mul_self _ _⟩` and prove the remaining obligations.

Simplify using `only [Equiv.swap_apply_def]`. Apply the tactic sequence `split_ifs <;> simp_all [Fin.ext_iff, Fin.val_rev, lo] <;> omega`.
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
