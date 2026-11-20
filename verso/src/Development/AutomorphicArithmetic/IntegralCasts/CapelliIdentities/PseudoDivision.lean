import Mathlib

universe u

/- English proof (translation)
Introduce `R _ g p hg`. Proceed by induction on `p using (Polynomial.degree_lt_wf (R := R)).induction with`. Consider the case `_ p ih`. Distinguish the cases in `h : p.degree < g.degree`. Conclude with `⟨0, 0, p, by simp, h⟩`.

Establish `hle : g.degree ≤ p.degree` using `not_lt.mp h`. Establish `hp : p ≠ 0`. Introduce and unpack `rfl`. Rewrite `hle` using `[Polynomial.degree_zero, le_bot_iff, Polynomial.degree_eq_bot]`. Conclude with `hg hle`.

Take `⟨d, hd⟩` from `Nat.exists_eq_add_of_le (Polynomial.natDegree_le_natDegree hle)`. Establish `hlt : (Polynomial.C g.leadingCoeff * p - g * Polynomial.monomial d p.leadingCoeff).degree < p.degree`. Rewrite using `[Polynomial.degree_eq_natDegree hp, Polynomial.degree_lt_iff_coeff_zero]`. Introduce `m hm`. Take `⟨j, rfl⟩ : ∃ j, m = j + d` from `⟨m - d, by omega⟩`.

Rewrite using `[Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_mul_monomial]`. Break down `Nat.eq_or_lt_of_le hm with he | hl` into its components or cases. Establish `hj : j = g.natDegree` using `by omega`. Rewrite using `[← he, hj]`. Conclude with `sub_self _`.

Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt hl, Polynomial.coeff_eq_zero_of_natDegree_lt (show g.natDegree < j by omega)]`. Simplify using the standard rewrite rules. Take `⟨k, q, r, he, hr⟩` from `ih _ hlt`. Use `⟨k + 1, q + Polynomial.C (g.leadingCoeff ^ k) * Polynomial.monomial d p.leadingCoeff, r, ?_, hr⟩` and prove the remaining obligations. Rewrite using `[pow_succ, Polynomial.C_mul]`.

Take the linear combination `he`.
-/
theorem UpperTheory.pseudo_division :
    ∀ (R : Type u) [CommRing R] (g p : Polynomial R), g ≠ 0 → ∃ (k : ℕ) (q r : Polynomial R), Polynomial.C (g.leadingCoeff ^ k) * p = g * q + r ∧ r.degree < g.degree := by
  intro R _ g p hg
  induction p using (Polynomial.degree_lt_wf (R := R)).induction with
  | _ p ih =>
    by_cases h : p.degree < g.degree
    · exact ⟨0, 0, p, by simp, h⟩
    · have hle : g.degree ≤ p.degree := not_lt.mp h
      have hp : p ≠ 0 := by
        rintro rfl
        rw [Polynomial.degree_zero, le_bot_iff, Polynomial.degree_eq_bot] at hle
        exact hg hle
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Polynomial.natDegree_le_natDegree hle)
      have hlt : (Polynomial.C g.leadingCoeff * p
          - g * Polynomial.monomial d p.leadingCoeff).degree < p.degree := by
        rw [Polynomial.degree_eq_natDegree hp, Polynomial.degree_lt_iff_coeff_zero]
        intro m hm
        obtain ⟨j, rfl⟩ : ∃ j, m = j + d := ⟨m - d, by omega⟩
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_mul_monomial]
        rcases Nat.eq_or_lt_of_le hm with he | hl
        · have hj : j = g.natDegree := by omega
          rw [← he, hj]
          exact sub_self _
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hl,
            Polynomial.coeff_eq_zero_of_natDegree_lt (show g.natDegree < j by omega)]
          simp
      obtain ⟨k, q, r, he, hr⟩ := ih _ hlt
      refine ⟨k + 1, q + Polynomial.C (g.leadingCoeff ^ k) * Polynomial.monomial d p.leadingCoeff,
        r, ?_, hr⟩
      rw [pow_succ, Polynomial.C_mul]
      linear_combination he
