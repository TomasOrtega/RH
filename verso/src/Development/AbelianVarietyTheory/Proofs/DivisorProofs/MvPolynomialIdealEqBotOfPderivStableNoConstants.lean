import Mathlib

namespace GlobalTheory

open MvPolynomial Finsupp

/- English proof (translation)
Introduce `R _ _ _ r I hI hC`. Establish `key : ∀ n : ℕ, ∀ P ∈ I, P.totalDegree = n → P = 0`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`.

Introduce `P hP h`. Assume the negation of the conclusion as `hne`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Rewrite `h` using `[totalDegree_eq_zero_iff_eq_C]`.

Apply `hne` to reduce the goal to its premises. Rewrite `hP`, the goal using `[h]`. Rewrite using `[hC _ hP, C_0]`. Take `⟨m, hm, hmd⟩` from `Finset.exists_mem_eq_sup P.support (support_nonempty.mpr hne) (fun s => s.sum fun _ e => e)`. Establish `hdeg : (m.sum fun _ e => e) = n` using `by rw [← h, totalDegree, hmd]`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, m i ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hm0 : m = 0` using `Finsupp.ext hcon`. Substitute `hm0` using the available equality.

Simplify using `at hdeg`. Use linear arithmetic over natural numbers and integers. Establish `hQ : pderiv i P ∈ I` using `hI P hP i`. Establish `hQne : pderiv i P ≠ 0`. Introduce `h0`.

Establish `hc` using `coeff_pderiv (i := i) P (m - single i 1)`. Rewrite `hc` using `[h0, coeff_zero, sub_add_single_one_cancel hi]`. Establish `hcm : coeff m P ≠ 0` using `MvPolynomial.mem_support_iff.mp hm`. Establish `hk : (((m - single i 1 : Fin r →₀ ℕ) i : ℕ) : R) + 1 ≠ 0` using `Nat.cast_add_one_ne_zero _`. Conclude with `(mul_ne_zero hcm hk) hc.symm`.

Establish `hlt : (pderiv i P).totalDegree < n`. Establish `hle : (pderiv i P).totalDegree ≤ n - 1`. Apply `Finset.sup_le` to reduce the goal to its premises. Introduce `s hs`. Establish `hs'` using `MvPolynomial.mem_support_iff.mp hs`.

Rewrite `hs'` using `[coeff_pderiv]`. Establish `hsupp : s + single i 1 ∈ P.support` using `MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hs')`. Establish `hd` using `le_totalDegree hsupp`. Rewrite `hd` using `[Finsupp.sum_add_index' (by simp) (by intros; rfl), Finsupp.sum_single_index rfl, h]`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Conclude with `hQne (ih _ hlt _ hQ rfl)`. Rewrite using `[eq_bot_iff]`. Introduce `P hP`. Rewrite using `[Ideal.mem_bot]`.

Conclude with `key _ P hP rfl`.
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
