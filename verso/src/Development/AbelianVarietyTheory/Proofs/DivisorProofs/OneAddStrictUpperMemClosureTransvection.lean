import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSubst
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef

namespace GlobalTheory.UpperTransvection

/- English proof (translation)
Reduce the argument to an intermediate assertion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. By extensionality, compare the relevant components. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Substitute using the available equality. Simplify to obtain the desired conclusion from the available facts. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem upper_mem_closure (R : Type) [CommRing R] (N : ℕ) (c : Matrix (Fin N) (Fin N) R)
    (hc : ∀ a b, b ≤ a → c a b = 0) :
    1 + c ∈ Submonoid.closure
      {M | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r} := by
  classical
  set S := Submonoid.closure
      {M : Matrix (Fin N) (Fin N) R | ∃ (a b : Fin N) (r : R), a ≠ b ∧ M = Matrix.transvection a b r}
  suffices key : ∀ n : ℕ, ∀ c : Matrix (Fin N) (Fin N) R, (∀ a b, b ≤ a → c a b = 0) →
      (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0).card ≤ n → 1 + c ∈ S from
    key _ c hc le_rfl
  intro n
  induction n with
  | zero =>
    intro c _ hcard
    have hc0 : c = 0 := by
      ext i j
      by_contra h
      have : (i, j) ∈ (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0) := by
        simpa using h
      rw [Nat.le_zero, Finset.card_eq_zero] at hcard
      simp [hcard] at this
    subst hc0
    simpa using S.one_mem
  | succ n ih =>
    intro c hc hcard
    set T := (Finset.univ.filter fun p : Fin N × Fin N => c p.1 p.2 ≠ 0) with hT
    rcases T.eq_empty_or_nonempty with hE | hne
    · exact ih c hc (by rw [← hT, hE]; simp)
    obtain ⟨p, hpT, hpmin⟩ := Finset.exists_min_image T (fun p => p.1) hne
    obtain ⟨a, b⟩ := p
    have hab : c a b ≠ 0 := by simpa [hT] using hpT
    have hlt : a < b := by
      by_contra h
      exact hab (hc a b (not_lt.mp h))

    have hcol : ∀ i, c i a = 0 := by
      intro i
      by_contra h
      have hi : (i, a) ∈ T := by simpa [hT] using h
      have h1 := hpmin _ hi
      have h2 : a ≤ i := h1
      exact h (hc i a h2)
    set r := c a b
    set c' := c - Matrix.single a b r with hc'
    have hc'_apply : ∀ i j, c' i j = if i = a ∧ j = b then 0 else c i j := by
      intro i j
      simp only [hc', Matrix.sub_apply, Matrix.single_apply]
      by_cases h : i = a ∧ j = b
      · obtain ⟨rfl, rfl⟩ := h; simp [r]
      · have h' : ¬ (a = i ∧ b = j) := fun ⟨h1, h2⟩ => h ⟨h1.symm, h2.symm⟩
        simp [h, h']
    have hc'up : ∀ i j, j ≤ i → c' i j = 0 := by
      intro i j hji
      rw [hc'_apply]; split_ifs
      · rfl
      · exact hc i j hji
    have hT' : (Finset.univ.filter fun p : Fin N × Fin N => c' p.1 p.2 ≠ 0) ⊆ T.erase (a, b) := by
      intro q hq
      obtain ⟨i, j⟩ := q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
      rw [hc'_apply] at hq
      split_ifs at hq with h
      · exact absurd rfl hq
      · rw [Finset.mem_erase]
        refine ⟨?_, by simpa [hT] using hq⟩
        intro heq
        simp only [Prod.mk.injEq] at heq
        exact h heq
    have hcard' : (Finset.univ.filter fun p : Fin N × Fin N => c' p.1 p.2 ≠ 0).card ≤ n := by
      have := Finset.card_le_card hT'
      rw [Finset.card_erase_of_mem hpT] at this
      omega
    have hmem' : 1 + c' ∈ S := ih c' hc'up hcard'
    have hcolz : c' * Matrix.single a b r = 0 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro k _
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        rw [hc'_apply]; split_ifs
        · simp
        · rw [hcol]; simp
      · simp
    have heq : 1 + c = (1 + c') * Matrix.transvection a b r := by
      rw [Matrix.transvection, add_mul, one_mul, mul_add, mul_one, hcolz, add_zero, hc']
      abel
    rw [heq]
    refine S.mul_mem hmem' (Submonoid.subset_closure ⟨a, b, r, hlt.ne, rfl⟩)

end GlobalTheory.UpperTransvection
