import Mathlib

open Matrix

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Substitute using the available equality. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Substitute using the available equality. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem laurentMonomial_of_multiplicative :
    ∀ (n : ℕ) (χ : (Fin n → ℂ) → ℂ), χ 1 = 1 →
      (∀ s t : Fin n → ℂ, (∀ i, s i ≠ 0) → (∀ i, t i ≠ 0) → χ (s * t) = χ s * χ t) →
      (∀ i : Fin n, ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ (Pi.mulSingle i t) = t ^ k) →
      ∃ μ : Fin n → ℤ, ∀ d : Fin n → ℂ, (∀ i, d i ≠ 0) → χ d = ∏ i, d i ^ μ i := by
  intro n χ h1 hmul hk
  choose k hk using hk
  refine ⟨k, fun d hd => ?_⟩
  have hne : ∀ (s : Finset (Fin n)) (i : Fin n), (∏ j ∈ s, Pi.mulSingle j (d j)) i ≠ 0 := by
    intro s i
    rw [Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    rw [Pi.mulSingle_apply]
    split_ifs with h
    · subst h; exact hd _
    · exact one_ne_zero
  have key : ∀ s : Finset (Fin n), χ (∏ i ∈ s, Pi.mulSingle i (d i)) = ∏ i ∈ s, d i ^ k i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using h1
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.prod_insert ha, hmul _ _ ?_ (hne s), hk a (d a) (hd a), ih]
      intro i
      rw [Pi.mulSingle_apply]
      split_ifs with h
      · subst h; exact hd _
      · exact one_ne_zero
  have := key Finset.univ
  rwa [Finset.univ_prod_mulSingle] at this

end GlobalTheory
