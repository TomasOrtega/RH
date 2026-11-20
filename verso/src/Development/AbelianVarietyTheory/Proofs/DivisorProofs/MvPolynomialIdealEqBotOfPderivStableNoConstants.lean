import Mathlib

namespace GlobalTheory

open MvPolynomial Finsupp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the indicated hypotheses using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Substitute using the available equality. Simplify using the standard rewrite rules.

Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem mvPolynomial_ideal_eq_bot_of_pderiv_stable :
    ∀ {R : Type} [CommRing R] [IsDomain R] [CharZero R] (r : ℕ)
    (I : Ideal (MvPolynomial (Fin r) R)),
  (∀ P ∈ I, ∀ i, MvPolynomial.pderiv i P ∈ I) → (∀ a : R, MvPolynomial.C a ∈ I → a = 0) → I = ⊥ := by
  intro R _ _ _ r I hI hC
  have key : ∀ n : ℕ, ∀ P ∈ I, P.totalDegree = n → P = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro P hP h
    by_contra hne
    by_cases hn : n = 0
    · subst hn
      rw [totalDegree_eq_zero_iff_eq_C] at h
      apply hne
      rw [h] at hP ⊢
      rw [hC _ hP, C_0]
    · obtain ⟨m, hm, hmd⟩ := Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hne)
        (fun s => s.sum fun _ e => e)
      have hdeg : (m.sum fun _ e => e) = n := by rw [← h, totalDegree, hmd]
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have hm0 : m = 0 := Finsupp.ext hcon
        subst hm0
        simp at hdeg
        omega
      have hQ : pderiv i P ∈ I := hI P hP i
      have hQne : pderiv i P ≠ 0 := by
        intro h0
        have hc := coeff_pderiv (i := i) P (m - single i 1)
        rw [h0, coeff_zero, sub_add_single_one_cancel hi] at hc
        have hcm : coeff m P ≠ 0 := MvPolynomial.mem_support_iff.mp hm
        have hk : (((m - single i 1 : Fin r →₀ ℕ) i : ℕ) : R) + 1 ≠ 0 :=
          Nat.cast_add_one_ne_zero _
        exact (mul_ne_zero hcm hk) hc.symm
      have hlt : (pderiv i P).totalDegree < n := by
        have hle : (pderiv i P).totalDegree ≤ n - 1 := by
          apply Finset.sup_le
          intro s hs
          have hs' := MvPolynomial.mem_support_iff.mp hs
          rw [coeff_pderiv] at hs'
          have hsupp : s + single i 1 ∈ P.support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hs')
          have hd := le_totalDegree hsupp
          rw [Finsupp.sum_add_index' (by simp) (by intros; rfl), Finsupp.sum_single_index rfl, h] at hd
          omega
        omega
      exact hQne (ih _ hlt _ hQ rfl)
  rw [eq_bot_iff]
  intro P hP
  rw [Ideal.mem_bot]
  exact key _ P hP rfl

end GlobalTheory
