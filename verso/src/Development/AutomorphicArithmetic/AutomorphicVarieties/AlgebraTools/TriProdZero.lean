import Mathlib

open Polynomial Matrix IsLocalRing TensorProduct

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.tri_prod_zero :
    ∀ {R : Type} [CommRing R] {n : ℕ} (u : Fin n → Matrix (Fin n) (Fin n) R), (∀ k i j, j < i → u k i j = 0) → (∀ k, u k k k = 0) → (List.ofFn u).prod = 0 := by
  intro R _ n u h1 h2
  have key : ∀ m, m ≤ n → ∀ i j : Fin n, j.val < m →
      ((List.ofFn u).take m).prod i j = 0 := by
    intro m
    induction m with
    | zero => intro _ i j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm i j hj
      have hlen : m < (List.ofFn u).length := by
        rw [List.length_ofFn]; omega
      rw [List.prod_take_succ _ _ hlen, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l.val < m
      · rw [ih (by omega) i l hl, zero_mul]
      · have hu : (List.ofFn u)[m] = u ⟨m, by omega⟩ := by
          simp
        rw [hu]
        by_cases hjl : j < l
        · rw [h1 _ _ _ hjl, mul_zero]
        · have hjl' : l.val ≤ j.val := Fin.le_def.mp (not_lt.mp hjl)
          have e1 : l = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
          have e2 : j = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
          rw [e1, e2, h2, mul_zero]
  ext i j
  have := key n le_rfl i j j.isLt
  rw [List.take_of_length_le (by simp)] at this
  simpa using this
