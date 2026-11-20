import Formalism.LogVandermondeBounds.EvenOddPowerQuotientEqualityCases

namespace Formalism.LogVandermondeBounds.TaylorLogMetric

open Finset

/- English proof (translation)
Establish `hq : 1 ≤ x ^ 2` using `by nlinarith`. Establish `step : ∀ i j : ℕ, (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) ≤ (x ^ 2) ^ i + x * (x ^ 2) ^ (j + 1) - (x ^ 2 - 1) * ((i : ℚ) + (j + 1 : ℕ) + 1)`. Introduce `i j`. Establish `hA : 1 ≤ (x ^ 2) ^ j` using `one_le_pow₀ hq`. Establish `hB : 1 ≤ x * (x ^ 2) ^ j` using `by nlinarith`.

Use `push_cast`. Rewrite using `[pow_succ (x ^ 2) j]`. Establish `hq0 : 0 ≤ x ^ 2 - 1` using `by linarith`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_right hB hq0]`. Establish `mono : ∀ i j k : ℕ, (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) ≤ (x ^ 2) ^ i + x * (x ^ 2) ^ (j + k) - (x ^ 2 - 1) * ((i : ℚ) + (j + k : ℕ) + 1)`.

Introduce `i j k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih => exact ih.trans (by simpa [Nat.add_assoc] using step i (j + k))`. Establish `diag : ∀ m : ℕ, x ^ 3 - 2 * x ^ 2 + 3 ≤ (x ^ 2) ^ (m + 1) + x * (x ^ 2) ^ (m + 1) - (x ^ 2 - 1) * (((m + 1 : ℕ) : ℚ) + (m + 1 : ℕ) + 1)`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => push_cast`. Put the polynomial expressions in normal form. Combine the linear equalities and inequalities to obtain the conclusion.

Consider the case `succ m ih`. Establish `hA : 1 ≤ (x ^ 2) ^ (m + 1)` using `one_le_pow₀ hq`. Establish `hB : 2 ≤ (x ^ 2) ^ (m + 1) + x * (x ^ 2) ^ (m + 1)` using `by nlinarith`. Use `ih.trans ?_` and prove the remaining obligations. Move the coercions through the operations in `at *`.

Rewrite using `[pow_succ (x ^ 2) (m + 1)]`. Use the polynomial consequences of the given equalities and inequalities. Introduce `i j hij hne`. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Establish `hj : 1 ≤ j`.

Break down `Nat.eq_zero_or_pos j with rfl | hj` into its components or cases. Conclude with `absurd rfl hne`. Conclude with `hj`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hj`. Use `le_trans ?_ (mono 0 1 k)` and prove the remaining obligations.

Use `push_cast`. Put the polynomial expressions in normal form. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le hi`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hij`.

Use `mono (1 + m) (1 + m) k` as an intermediate fact. Establish `h2` using `diag m`. Rewrite `*` using `[Nat.add_comm 1 m]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma key_ineq (x : ℚ) (hx : 2 ≤ x) :
    ∀ i j : ℕ, i ≤ j → (i, j) ≠ (0, 0) →
      x ^ 3 - 2 * x ^ 2 + 3 ≤ (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) := by
  have hq : 1 ≤ x ^ 2 := by nlinarith

  have step : ∀ i j : ℕ, (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) ≤
      (x ^ 2) ^ i + x * (x ^ 2) ^ (j + 1) - (x ^ 2 - 1) * ((i : ℚ) + (j + 1 : ℕ) + 1) := by
    intro i j
    have hA : 1 ≤ (x ^ 2) ^ j := one_le_pow₀ hq
    have hB : 1 ≤ x * (x ^ 2) ^ j := by nlinarith
    push_cast
    rw [pow_succ (x ^ 2) j]
    have hq0 : 0 ≤ x ^ 2 - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hB hq0]
  have mono : ∀ i j k : ℕ, (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) ≤
      (x ^ 2) ^ i + x * (x ^ 2) ^ (j + k) - (x ^ 2 - 1) * ((i : ℚ) + (j + k : ℕ) + 1) := by
    intro i j k
    induction k with
    | zero => simp
    | succ k ih => exact ih.trans (by simpa [Nat.add_assoc] using step i (j + k))

  have diag : ∀ m : ℕ, x ^ 3 - 2 * x ^ 2 + 3 ≤
      (x ^ 2) ^ (m + 1) + x * (x ^ 2) ^ (m + 1) - (x ^ 2 - 1) * (((m + 1 : ℕ) : ℚ) + (m + 1 : ℕ) + 1) := by
    intro m
    induction m with
    | zero => push_cast; ring_nf; linarith
    | succ m ih =>
      have hA : 1 ≤ (x ^ 2) ^ (m + 1) := one_le_pow₀ hq
      have hB : 2 ≤ (x ^ 2) ^ (m + 1) + x * (x ^ 2) ^ (m + 1) := by nlinarith
      refine ih.trans ?_
      push_cast at *
      rw [pow_succ (x ^ 2) (m + 1)]
      nlinarith
  intro i j hij hne
  rcases Nat.eq_zero_or_pos i with rfl | hi
  ·
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact absurd rfl hne
      · exact hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    refine le_trans ?_ (mono 0 1 k)
    push_cast; ring_nf; linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    have := mono (1 + m) (1 + m) k
    have h2 := diag m
    rw [Nat.add_comm 1 m] at *
    linarith

/- English proof (translation)
Use the polynomial consequences of the given equalities and inequalities.
-/
lemma sq_ge_two (p : ℕ) (hp : 2 ≤ p) : 2 ≤ p ^ 2 := by nlinarith

/- English proof (translation)
Establish `h : ∃ j', (p ^ 2) ^ j = (p ^ 2) ^ j'` using `⟨j, rfl⟩`. Unfold `coefL`. Rewrite using `[dif_pos h]`. Establish `hj : j = Classical.choose h` using `Nat.pow_right_injective (sq_ge_two p hp) (Classical.choose_spec h)`. Rewrite using `[← hj]`.
-/
lemma coefL_pow (p j : ℕ) (hp : 2 ≤ p) : coefL p ((p ^ 2) ^ j) = 1 / (p : ℚ) ^ j := by
  have h : ∃ j', (p ^ 2) ^ j = (p ^ 2) ^ j' := ⟨j, rfl⟩
  unfold coefL
  rw [dif_pos h]
  have hj : j = Classical.choose h := Nat.pow_right_injective (sq_ge_two p hp) (Classical.choose_spec h)
  rw [← hj]

/- English proof (translation)
Unfold `coefL`. Rewrite using `[dif_neg h]`.
-/
lemma coefL_zero (p a : ℕ) (h : ¬∃ j, a = (p ^ 2) ^ j) : coefL p a = 0 := by
  unfold coefL
  rw [dif_neg h]

/- English proof (translation)
Establish `h : ∃ j', p * (p ^ 2) ^ j = p * (p ^ 2) ^ j'` using `⟨j, rfl⟩`. Unfold `coefG`. Rewrite using `[dif_pos h]`. Establish `hj : j = Classical.choose h` using `Nat.pow_right_injective (sq_ge_two p hp) (Nat.eq_of_mul_eq_mul_left (by omega) (Classical.choose_spec h))`. Rewrite using `[← hj]`.
-/
lemma coefG_pow (p j : ℕ) (hp : 2 ≤ p) : coefG p (p * (p ^ 2) ^ j) = 1 / (p : ℚ) ^ (j + 1) := by
  have h : ∃ j', p * (p ^ 2) ^ j = p * (p ^ 2) ^ j' := ⟨j, rfl⟩
  unfold coefG
  rw [dif_pos h]
  have hj : j = Classical.choose h := Nat.pow_right_injective (sq_ge_two p hp)
    (Nat.eq_of_mul_eq_mul_left (by omega) (Classical.choose_spec h))
  rw [← hj]

/- English proof (translation)
Unfold `coefG`. Rewrite using `[dif_neg h]`.
-/
lemma coefG_zero (p a : ℕ) (h : ¬∃ j, a = p * (p ^ 2) ^ j) : coefG p a = 0 := by
  unfold coefG
  rw [dif_neg h]

/- English proof (translation)
Unfold `coefA`. Distinguish the cases in `hij : i ≤ j`. Establish `h : ∃ i' j', i' ≤ j' ∧ (p ^ 2) ^ i = (p ^ 2) ^ i' ∧ p * (p ^ 2) ^ j = p * (p ^ 2) ^ j'` using `⟨i, j, hij, rfl, rfl⟩`. Rewrite using `[dif_pos h, if_pos hij]`. Take `⟨-, h2, h3⟩` from `Classical.choose_spec (Classical.choose_spec h)`.

Establish `hi : i = Classical.choose h` using `Nat.pow_right_injective (sq_ge_two p hp) h2`. Establish `hj : j = Classical.choose (Classical.choose_spec h)` using `Nat.pow_right_injective (sq_ge_two p hp) (Nat.eq_of_mul_eq_mul_left (by omega) h3)`. Rewrite using `[← hj, ← hi]`. Rewrite using `[if_neg hij, dif_neg]`. Introduce and unpack `⟨i', j', h1, h2, h3⟩`.

Establish `hi : i = i'` using `Nat.pow_right_injective (sq_ge_two p hp) h2`. Establish `hj : j = j'` using `Nat.pow_right_injective (sq_ge_two p hp) (Nat.eq_of_mul_eq_mul_left (by omega) h3)`. Substitute `hi hj` using the available equality. Conclude with `hij h1`.
-/
lemma coefA_pow (p i j : ℕ) (hp : 2 ≤ p) :
    coefA p ((p ^ 2) ^ i) (p * (p ^ 2) ^ j) = if i ≤ j then 1 / (p : ℚ) ^ (i + j + 1) else 0 := by
  unfold coefA
  by_cases hij : i ≤ j
  · have h : ∃ i' j', i' ≤ j' ∧ (p ^ 2) ^ i = (p ^ 2) ^ i' ∧ p * (p ^ 2) ^ j = p * (p ^ 2) ^ j' :=
      ⟨i, j, hij, rfl, rfl⟩
    rw [dif_pos h, if_pos hij]
    obtain ⟨-, h2, h3⟩ := Classical.choose_spec (Classical.choose_spec h)
    have hi : i = Classical.choose h := Nat.pow_right_injective (sq_ge_two p hp) h2
    have hj : j = Classical.choose (Classical.choose_spec h) :=
      Nat.pow_right_injective (sq_ge_two p hp) (Nat.eq_of_mul_eq_mul_left (by omega) h3)
    rw [← hj, ← hi]
  · rw [if_neg hij, dif_neg]
    rintro ⟨i', j', h1, h2, h3⟩
    have hi : i = i' := Nat.pow_right_injective (sq_ge_two p hp) h2
    have hj : j = j' := Nat.pow_right_injective (sq_ge_two p hp) (Nat.eq_of_mul_eq_mul_left (by omega) h3)
    subst hi hj
    exact hij h1

/- English proof (translation)
Unfold `coefA`. Rewrite using `[dif_neg h]`.
-/
lemma coefA_zero (p a b : ℕ) (h : ¬∃ i j, i ≤ j ∧ a = (p ^ 2) ^ i ∧ b = p * (p ^ 2) ^ j) :
    coefA p a b = 0 := by
  unfold coefA
  rw [dif_neg h]

/- English proof (translation)
Introduce `p hp`. Establish `hp2 : 2 ≤ p` using `hp.two_le`. Establish `hp0 : 0 < p` using `hp.pos`. Establish `hpq : (p : ℚ) ≠ 0` using `by exact_mod_cast hp0.ne'`. Prove the components needed by the constructor for the conclusion.

Introduce `a`. Distinguish the cases in `hd : p ∣ a`. Take `⟨c, rfl⟩` from `hd`. Rewrite using `[if_pos (dvd_mul_right p c), Nat.mul_div_cancel_left c hp0]`. Establish `ha1 : p * c ≠ 1`.

Introduce `h`. Break down `c with _ | c` into its components or cases. Simplify using `at h`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[if_neg ha1, sub_zero]`.

Distinguish the cases in `hc : ∃ k, c = p * (p ^ 2) ^ k`. Take `⟨k, rfl⟩` from `hc`. Rewrite using `[coefG_pow p k hp2, show p * (p * (p ^ 2) ^ k) = (p ^ 2) ^ (k + 1) by ring, coefL_pow p _ hp2]`. Rewrite using `[coefG_zero p c hc, coefL_zero]`. Introduce and unpack `⟨j, hj⟩`.

Break down `j with _ | k` into its components or cases. Rewrite `hj` using `[pow_zero]`. Conclude with `ha1 hj`. Apply `hc` to reduce the goal to its premises. Use `⟨k, ?_⟩` and prove the remaining obligations.

Establish `: p * c = p * (p * (p ^ 2) ^ k)` using `by rw [hj]; ring`. Conclude with `Nat.eq_of_mul_eq_mul_left hp0 this`. Rewrite using `[if_neg hd]`. Distinguish the cases in `ha : a = 1`. Substitute `ha` using the available equality.

Establish `h1` using `coefL_pow p 0 hp2`. Rewrite `h1` using `[pow_zero, pow_zero]`. Rewrite using `[if_pos rfl, h1]`. Evaluate the numerical expressions. Rewrite using `[if_neg ha, sub_zero, coefL_zero]`.

Introduce and unpack `⟨j, rfl⟩`. Break down `j with _ | k` into its components or cases. Conclude with `ha (pow_zero _)`. Conclude with `hd (dvd_pow (dvd_pow_self p two_ne_zero) (Nat.succ_ne_zero k))`. Introduce `a b`.

Distinguish the cases in `hA : ∃ i, a = p * (p ^ 2) ^ i`. Take `⟨i, rfl⟩` from `hA`. Rewrite using `[coefG_pow p i hp2]`. Distinguish the cases in `hB : ∃ k, b = (p ^ 2) ^ k`. Take `⟨k, rfl⟩` from `hB`.

Simplify using `only [coefB]`. Rewrite using `[coefL_pow p k hp2, coefA_pow p k i hp2]`. Break down `k with _ | j` into its components or cases. Establish `hn : ¬(p ∣ p * (p ^ 2) ^ i ∧ p ∣ (p ^ 2) ^ 0)`. Introduce and unpack `⟨-, h⟩`.

Rewrite `h` using `[pow_zero, Nat.dvd_one]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_neg hn, if_pos (Nat.zero_le _)]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hb : (p ^ 2) ^ (j + 1) = p * (p * (p ^ 2) ^ j)` using `by ring`. Rewrite using `[hb, if_pos ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩, Nat.mul_div_cancel_left _ hp0, Nat.mul_div_cancel_left _ hp0, coefA_pow p i j hp2]`. Distinguish the cases in `h : i ≤ j`. Rewrite using `[if_pos h, if_neg (by omega)]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, if_pos (by omega)]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [coefB]`.

Rewrite using `[coefL_zero p b hB, coefA_zero p b _ (by rintro ⟨i', j', -, h2, -⟩; exact hB ⟨i', h2⟩)]`. Simplify using `only [mul_zero, sub_zero]`. Use `split_ifs with h`. Take `⟨-, c, rfl⟩` from `h`. Rewrite using `[Nat.mul_div_cancel_left _ hp0, Nat.mul_div_cancel_left _ hp0]`.

Apply `coefA_zero` to reduce the goal to its premises. Introduce and unpack `⟨i', j', -, -, h3⟩`. Conclude with `hB ⟨j' + 1, by rw [h3]; ring⟩`. Both sides reduce to the same expression. Simplify using `only [coefB]`.

Rewrite using `[coefG_zero p a hA, coefA_zero p b a (by rintro ⟨i', j', -, -, h3⟩; exact hA ⟨j', h3⟩)]`. Simplify using `only [zero_mul, zero_sub, mul_zero, neg_zero]`. Use `split_ifs with h`. Take `⟨⟨c, rfl⟩, -⟩` from `h`. Rewrite using `[Nat.mul_div_cancel_left _ hp0]`.

Apply `coefA_zero` to reduce the goal to its premises. Introduce and unpack `⟨i', j', -, h2, -⟩`. Conclude with `hA ⟨i', by rw [h2]⟩`. Both sides reduce to the same expression.
-/
theorem logarithm_series_coefficient_identities : LogarithmSeriesIdentities := by
  intro p hp
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : 0 < p := hp.pos
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
  constructor
  · intro a
    by_cases hd : p ∣ a
    · obtain ⟨c, rfl⟩ := hd
      rw [if_pos (dvd_mul_right p c), Nat.mul_div_cancel_left c hp0]
      have ha1 : p * c ≠ 1 := by
        intro h
        rcases c with _ | c
        · simp at h
        · nlinarith
      rw [if_neg ha1, sub_zero]
      by_cases hc : ∃ k, c = p * (p ^ 2) ^ k
      · obtain ⟨k, rfl⟩ := hc
        rw [coefG_pow p k hp2, show p * (p * (p ^ 2) ^ k) = (p ^ 2) ^ (k + 1) by ring, coefL_pow p _ hp2]
      · rw [coefG_zero p c hc, coefL_zero]
        rintro ⟨j, hj⟩
        rcases j with _ | k
        · rw [pow_zero] at hj
          exact ha1 hj
        · apply hc
          refine ⟨k, ?_⟩
          have : p * c = p * (p * (p ^ 2) ^ k) := by rw [hj]; ring
          exact Nat.eq_of_mul_eq_mul_left hp0 this
    · rw [if_neg hd]
      by_cases ha : a = 1
      · subst ha
        have h1 := coefL_pow p 0 hp2
        rw [pow_zero, pow_zero] at h1
        rw [if_pos rfl, h1]
        norm_num
      · rw [if_neg ha, sub_zero, coefL_zero]
        rintro ⟨j, rfl⟩
        rcases j with _ | k
        · exact ha (pow_zero _)
        · exact hd (dvd_pow (dvd_pow_self p two_ne_zero) (Nat.succ_ne_zero k))
  · intro a b
    by_cases hA : ∃ i, a = p * (p ^ 2) ^ i
    · obtain ⟨i, rfl⟩ := hA
      rw [coefG_pow p i hp2]
      by_cases hB : ∃ k, b = (p ^ 2) ^ k
      · obtain ⟨k, rfl⟩ := hB
        simp only [coefB]
        rw [coefL_pow p k hp2, coefA_pow p k i hp2]
        rcases k with _ | j
        · have hn : ¬(p ∣ p * (p ^ 2) ^ i ∧ p ∣ (p ^ 2) ^ 0) := by
            rintro ⟨-, h⟩
            rw [pow_zero, Nat.dvd_one] at h
            omega
          rw [if_neg hn, if_pos (Nat.zero_le _)]
          field_simp
          ring
        · have hb : (p ^ 2) ^ (j + 1) = p * (p * (p ^ 2) ^ j) := by ring
          rw [hb, if_pos ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩, Nat.mul_div_cancel_left _ hp0,
            Nat.mul_div_cancel_left _ hp0, coefA_pow p i j hp2]
          by_cases h : i ≤ j
          · rw [if_pos h, if_neg (by omega)]
            field_simp
            ring
          · rw [if_neg h, if_pos (by omega)]
            field_simp
            ring
      · simp only [coefB]
        rw [coefL_zero p b hB, coefA_zero p b _ (by rintro ⟨i', j', -, h2, -⟩; exact hB ⟨i', h2⟩)]
        simp only [mul_zero, sub_zero]
        split_ifs with h
        · obtain ⟨-, c, rfl⟩ := h
          rw [Nat.mul_div_cancel_left _ hp0, Nat.mul_div_cancel_left _ hp0]
          apply coefA_zero
          rintro ⟨i', j', -, -, h3⟩
          exact hB ⟨j' + 1, by rw [h3]; ring⟩
        · rfl
    · simp only [coefB]
      rw [coefG_zero p a hA, coefA_zero p b a (by rintro ⟨i', j', -, -, h3⟩; exact hA ⟨j', h3⟩)]
      simp only [zero_mul, zero_sub, mul_zero, neg_zero]
      split_ifs with h
      · obtain ⟨⟨c, rfl⟩, -⟩ := h
        rw [Nat.mul_div_cancel_left _ hp0]
        apply coefA_zero
        rintro ⟨i', j', -, h2, -⟩
        exact hA ⟨i', by rw [h2]⟩
      · rfl

end Formalism.LogVandermondeBounds.TaylorLogMetric
