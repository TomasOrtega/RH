import Mathlib

namespace GlobalTheory.IntegerShiftSingle

universe u_1 u_2 u_3

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem shift_single_int {ι : Type u_1} {R : Type u_2} {E : Type u_3} [DecidableEq ι] [Ring R]
    {F : (ι → R) → E} (h : ∀ (i : ι) (x : ι → R), F (x + Pi.single i (1 : R)) = F x)
    (i : ι) (k : ℤ) : ∀ x : ι → R, F (x + Pi.single i ((k : ℤ) : R)) = F x := by
  induction k using Int.induction_on with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    have : x + Pi.single i (((m : ℤ) + 1 : ℤ) : R) = (x + Pi.single i ((m : ℤ) : R)) + Pi.single i (1 : R) := by
      rw [Int.cast_add, Int.cast_one, Pi.single_add, add_assoc]
    rw [this, h, ih]
  | pred m ih =>
    intro x
    have : x + Pi.single i ((-(m : ℤ) : ℤ) : R) = (x + Pi.single i ((-(m : ℤ) - 1 : ℤ) : R)) + Pi.single i (1 : R) := by
      rw [add_assoc, ← Pi.single_add]
      congr 2
      push_cast
      first | rfl | ring | abel | simp
    rw [← ih x, this, h]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem main {ι : Type u_1} {R : Type u_2} {E : Type u_3} [Fintype ι] [inst : DecidableEq ι] [inst_1 : Ring R]
    {F : (ι → R) → E} : (∀ (i : ι) (x : ι → R), F (x + Pi.single i (1 : R)) = F x) →
    ∀ (n : ι → ℤ) (x : ι → R), F (x + fun (i : ι) ↦ (↑(n i) : R)) = F x := by
  intro h n x
  have key : ∀ s : Finset ι, ∀ y : ι → R, F (y + ∑ i ∈ s, Pi.single i ((n i : ℤ) : R)) = F y := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      rw [Finset.sum_insert ha, ← add_assoc, ih, shift_single_int h]
  have hsum : (fun i : ι => ((n i : ℤ) : R)) = ∑ i ∈ Finset.univ, Pi.single i ((n i : ℤ) : R) := by
    rw [Finset.univ_sum_single]
  rw [hsum]
  exact key Finset.univ x

end GlobalTheory.IntegerShiftSingle
