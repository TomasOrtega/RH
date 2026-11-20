import Mathlib
open scoped Classical

namespace GlobalTheory.MultinomialCount

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem ofFn_cons_count {I : Type} {k : ℕ} (a : I) (t : Fin k → I) (i : I) :
    (List.ofFn (Fin.cons a t : Fin (k+1) → I)).count i = (List.ofFn t).count i + if a = i then 1 else 0 := by
  rw [List.ofFn_succ]
  simp [List.count_cons, Fin.cons_zero, Fin.cons_succ]

/- English proof (translation)
Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Assume the hypotheses and unpack their components.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Establish an intermediate fact. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem cons_iff {I : Type} {k : ℕ} (ν : I → ℕ) (a : I) (t : Fin k → I) :
    (∀ i, (List.ofFn (Fin.cons a t : Fin (k+1) → I)).count i = ν i) ↔
      (1 ≤ ν a ∧ ∀ i, (List.ofFn t).count i = Function.update ν a (ν a - 1) i) := by
  simp only [ofFn_cons_count]
  constructor
  · intro h
    have ha := h a
    simp only [if_true] at ha
    refine ⟨by omega, fun i => ?_⟩
    by_cases hi : i = a
    · subst hi; simp only [Function.update_self]; omega
    · have := h i
      rw [if_neg (Ne.symm hi)] at this
      simp only [Function.update_apply, hi, if_false]; omega
  · rintro ⟨h1, h⟩ i
    by_cases hi : i = a
    · subst hi; have := h i; simp only [Function.update_self] at this; simp only [if_true]; omega
    · have := h i
      simp only [Function.update_apply, hi, if_false] at this
      rw [if_neg (Ne.symm hi)]; omega

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion repeatedly using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_mul_prod_factorial : ∀ {I : Type} [Fintype I] (k : ℕ) (ν : I → ℕ), ∑ i, ν i = k →
    (Finset.univ.filter (fun s : Fin k → I => ∀ i, (List.ofFn s).count i = ν i)).card *
      ∏ i, (ν i).factorial = k.factorial := by
  intro I _ k
  induction k with
  | zero =>
    intro ν hν
    have h0 : ∀ i, ν i = 0 := fun i => (Finset.sum_eq_zero_iff.mp hν) i (Finset.mem_univ _)
    have : (Finset.univ.filter (fun s : Fin 0 → I => ∀ i, (List.ofFn s).count i = ν i)) = Finset.univ := by
      ext s; simp [h0]
    rw [this]; simp [h0]
  | succ k ih =>
    intro ν hν
    rw [Finset.card_filter, ← (Fin.consEquiv (fun _ : Fin (k+1) => I)).sum_comp, Fintype.sum_prod_type]
    have key : ∀ a : I, (∑ t : Fin k → I, if (∀ i, (List.ofFn (Fin.consEquiv (fun _ : Fin (k+1) => I) (a, t))).count i = ν i) then 1 else 0) *
        ∏ i, (ν i).factorial = ν a * k.factorial := by
      intro a
      have hc : ∀ t : Fin k → I, (∀ i, (List.ofFn (Fin.consEquiv (fun _ : Fin (k+1) => I) (a, t))).count i = ν i) ↔
          (1 ≤ ν a ∧ ∀ i, (List.ofFn t).count i = Function.update ν a (ν a - 1) i) := fun t => cons_iff ν a t
      simp_rw [hc]
      by_cases ha : 1 ≤ ν a
      · simp only [ha, true_and]
        rw [← Finset.card_filter]
        set μ := Function.update ν a (ν a - 1) with hμ
        have hs1 : ∑ i, μ i = (ν a - 1) + ∑ i ∈ Finset.univ \ {a}, ν i := by
          rw [hμ, Finset.sum_update_of_mem (Finset.mem_univ a)]
        have hs2 : ∑ i, ν i = ν a + ∑ i ∈ Finset.univ \ {a}, ν i :=
          Fintype.sum_eq_add_sum_compl a _
        have hμs : ∑ i, μ i = k := by omega
        have h1 : ∏ i, (μ i).factorial = (ν a - 1).factorial * ∏ i ∈ Finset.univ \ {a}, (ν i).factorial := by
          rw [Fintype.prod_eq_mul_prod_compl a]
          congr 1
          · simp [hμ]
          · apply Finset.prod_congr rfl
            intro i hi
            simp only [Finset.mem_compl, Finset.mem_singleton] at hi
            simp [hμ, Function.update_apply, hi]
        have h2 : ∏ i, (ν i).factorial = (ν a).factorial * ∏ i ∈ Finset.univ \ {a}, (ν i).factorial :=
          Fintype.prod_eq_mul_prod_compl a _
        have h3 : (ν a).factorial = ν a * (ν a - 1).factorial := (Nat.mul_factorial_pred (by omega)).symm
        have hi := ih μ hμs
        rw [h1] at hi
        rw [h2, h3, ← hi]
        ring
      · have : ν a = 0 := by omega
        simp [ha, this]
    rw [Finset.sum_mul]
    simp_rw [key]
    rw [← Finset.sum_mul, hν, Nat.factorial_succ]

end GlobalTheory.MultinomialCount
