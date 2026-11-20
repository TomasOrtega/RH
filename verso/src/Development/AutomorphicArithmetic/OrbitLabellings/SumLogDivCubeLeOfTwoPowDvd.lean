import Mathlib

open scoped BigOperators

/- English proof (translation)
Establish `hn0 : 0 < n` using `by linarith`. Establish `hu0 : 0 < u` using `by linarith`. Establish `hnu : 2 ≤ n * u` using `by nlinarith`. Establish `hl1 : 3 * (n * u) ≤ l` using `by nlinarith`. Establish `hl0 : 0 < l` using `by linarith`.

Establish `hlog2 : (1 / 2 : ℝ) ≤ Real.log n`. Use `Real.log_le_log (by norm_num) hn` as an intermediate fact. Use `Real.log_two_gt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hx : 0 < l / n` using `by positivity`.

Establish `h1 : Real.log l = Real.log n + Real.log (l / n)`. Rewrite using `[Real.log_div hl0.ne' hn0.ne']`. Expand and normalize the polynomial expressions, which then agree. Establish `h2` using `Real.log_le_sub_one_of_pos hx`. Establish `hx1 : 1 ≤ l / n`.

Rewrite using `[le_div_iff₀ hn0]`. Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : Real.log l ≤ 2 * (l / n) * Real.log n`. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hlog2)]`. Establish `h4 : Real.log l / l ^ 3 ≤ 2 * (l / n) * Real.log n / l ^ 3` using `by gcongr`.

Use `h4.trans ?_` and prove the remaining obligations. Establish `h5 : 2 * (l / n) * Real.log n / l ^ 3 = Real.log n / n ^ 3 * (2 * n ^ 2 / l ^ 2)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[h5]`. Establish `h6 : 2 * n ^ 2 / l ^ 2 ≤ 1 / 4 * (1 / u ^ 2)`.

Establish `: 1 / 4 * (1 / u ^ 2) = 1 / (4 * u ^ 2)` using `by field_simp`. Rewrite using `[this, div_le_div_iff₀ (by positivity) (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `: 0 ≤ Real.log n / n ^ 3` using `by positivity`. Use `gcongr`.
-/
private lemma log_div_cube_le_scaled (n l u : ℝ) (hn : 2 ≤ n) (hu : 1 ≤ u) (hl : 4 * n * u - 1 ≤ l) :
    Real.log l / l ^ 3 ≤ Real.log n / n ^ 3 * (1 / 4 * (1 / u ^ 2)) := by
  have hn0 : 0 < n := by linarith
  have hu0 : 0 < u := by linarith
  have hnu : 2 ≤ n * u := by nlinarith
  have hl1 : 3 * (n * u) ≤ l := by nlinarith
  have hl0 : 0 < l := by linarith
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log n := by
    have := Real.log_le_log (by norm_num) hn
    have := Real.log_two_gt_d9
    linarith
  have hx : 0 < l / n := by positivity
  have h1 : Real.log l = Real.log n + Real.log (l / n) := by
    rw [Real.log_div hl0.ne' hn0.ne']; ring
  have h2 := Real.log_le_sub_one_of_pos hx
  have hx1 : 1 ≤ l / n := by
    rw [le_div_iff₀ hn0]; nlinarith
  have h3 : Real.log l ≤ 2 * (l / n) * Real.log n := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sub_nonneg.2 hlog2)]
  have h4 : Real.log l / l ^ 3 ≤ 2 * (l / n) * Real.log n / l ^ 3 := by gcongr
  refine h4.trans ?_
  have h5 : 2 * (l / n) * Real.log n / l ^ 3 = Real.log n / n ^ 3 * (2 * n ^ 2 / l ^ 2) := by
    field_simp
  rw [h5]
  have h6 : 2 * n ^ 2 / l ^ 2 ≤ 1 / 4 * (1 / u ^ 2) := by
    have : 1 / 4 * (1 / u ^ 2) = 1 / (4 * u ^ 2) := by field_simp
    rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have : 0 ≤ Real.log n / n ^ 3 := by positivity
  gcongr

/- English proof (translation)
Proceed by induction on `M with`. Consider the case `zero => simp [Finset.sum_range_succ]`. Evaluate the numerical expressions. Consider the case `succ k ih`. Rewrite using `[show k + 1 + 2 = (k + 2) + 1 from rfl, Finset.sum_range_succ]`.

Establish `hk : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Establish `: 1 / ((k : ℝ) + 2) ^ 2 ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + 1)`. Rewrite using `[div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Use `push_cast`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma sum_inv_sq_range_le (M : ℕ) : ∑ u ∈ Finset.range (M + 2), (1 / (u : ℝ) ^ 2) ≤ 2 - 1 / ((M : ℝ) + 1) := by
  induction M with
  | zero => simp [Finset.sum_range_succ]; norm_num
  | succ k ih =>
    rw [show k + 1 + 2 = (k + 2) + 1 from rfl, Finset.sum_range_succ]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : 1 / ((k : ℝ) + 2) ^ 2 ≤ 1 / ((k : ℝ) + 1) - 1 / ((k : ℝ) + 1 + 1) := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast
    linarith

/- English proof (translation)
Introduce `e he S hS`. Use `set N : ℕ := 2 ^ (e + 2) with hN`. Establish `hN1 : 1 ≤ N` using `Nat.one_le_two_pow`. Establish `hNR : (N : ℝ) = 4 * (2 : ℝ) ^ e` using `by rw [hN]; push_cast; ring`. Establish `hn : (2 : ℝ) ≤ 2 ^ e`.

Combine the equalities or inequalities in the displayed calculation. Use `set f : ℕ → ℝ := fun l => Real.log l / (l : ℝ) ^ 3 with hf`. Establish `hf0 : ∀ l, 0 ≤ f l` using `fun l => div_nonneg (Real.log_natCast_nonneg l) (by positivity)`. Use `set c : ℝ := Real.log ((2 : ℝ) ^ e) / ((2 : ℝ) ^ e) ^ 3 with hc`. Establish `hc0 : 0 ≤ c` using `div_nonneg (Real.log_nonneg (by linarith)) (by positivity)`.

Use `set M := S.sup id with hM`. Use `set R := Finset.range (M + 2) with hR`. Establish `hsub : S ⊆ R.image (fun u => N * u + 1) ∪ R.image (fun u => N * u - 1)`. Introduce `l hl`. Establish `hlM : l ≤ M` using `Finset.le_sup (f := id) hl`.

Establish `hZ : (2 ^ (e + 2) : ℤ) = (N : ℤ)` using `by rw [hN]; push_cast; ring`. Establish `hN2 : 2 ≤ N`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.mem_union, Finset.mem_image, Finset.mem_image]`. Break down `hS l hl with h | h` into its components or cases.

Use `left`. Rewrite `h` using `[hZ]`. Establish `hl1 : 1 ≤ l`. Break down `Nat.eq_zero_or_pos l with rfl | h0` into its components or cases. It suffices to derive a contradiction.

Establish `h' : (N : ℤ) ∣ 1` using `by simpa using h`. Use `Int.le_of_dvd (by norm_num) h'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `h0`. Establish `h' : N ∣ l - 1`.

Rewrite using `[← Int.natCast_dvd_natCast, Nat.cast_sub hl1]`. Simplify using `using h`. Take `⟨u, hu⟩` from `h'`. Use `⟨u, ?_, by omega⟩` and prove the remaining obligations. Establish `: u ≤ N * u` using `Nat.le_mul_of_pos_left u hN1`.

Rewrite using `[hR, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Use `right`. Rewrite `h` using `[hZ]`. Establish `h' : N ∣ l + 1`.

Rewrite using `[← Int.natCast_dvd_natCast]`. Simplify using `using h`. Take `⟨u, hu⟩` from `h'`. Use `⟨u, ?_, by omega⟩` and prove the remaining obligations. Establish `: u ≤ N * u` using `Nat.le_mul_of_pos_left u hN1`.

Rewrite using `[hR, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Establish `hb : ∑ u ∈ R, c * (1 / 4 * (1 / (u : ℝ) ^ 2)) ≤ c / 2`. Rewrite using `[← Finset.mul_sum, ← Finset.mul_sum]`. Establish `h1` using `sum_inv_sq_range_le M`.

Establish `h2 : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1)` using `by positivity`. Establish `h3 : 1 / 4 * ∑ u ∈ R, (1 / (u : ℝ) ^ 2) ≤ 1 / 2` using `by rw [hR]; linarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hA : ∑ l ∈ R.image (fun u => N * u + 1), f l ≤ c / 2`. Use `(Finset.sum_image_le_of_nonneg (fun l _ => hf0 l)).trans (le_trans ?_ hb)` and prove the remaining obligations.

Use `Finset.sum_le_sum fun u _ => ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos u with rfl | h0` into its components or cases. Simplify using `[hf]`. Use `log_div_cube_le_scaled _ _ _ hn (by exact_mod_cast h0) ?_ push_cast; rw [hNR]; linarith` and prove the remaining obligations. Establish `hB : ∑ l ∈ R.image (fun u => N * u - 1), f l ≤ c / 2`.

Use `(Finset.sum_image_le_of_nonneg (fun l _ => hf0 l)).trans (le_trans ?_ hb)` and prove the remaining obligations. Use `Finset.sum_le_sum fun u _ => ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos u with rfl | h0` into its components or cases. Simplify using `[hf]`. Use `log_div_cube_le_scaled _ _ _ hn (by exact_mod_cast h0) ?_` and prove the remaining obligations.

Establish `: 1 ≤ N * u` using `Nat.mul_pos hN1 h0`. Rewrite using `[Nat.cast_sub this]`. Use `push_cast`. Rewrite using `[hNR]`. Establish `h1 : ∑ l ∈ S, f l ≤ _` using `Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => hf0 l)`.

Establish `h2` using `Finset.sum_union_inter (s₁ := R.image (fun u => N * u + 1)) (s₂ := R.image (fun u => N * u - 1)) (f := f)`. Establish `h3 : 0 ≤ ∑ l ∈ R.image (fun u => N * u + 1) ∩ R.image (fun u => N * u - 1), f l` using `Finset.sum_nonneg fun l _ => hf0 l`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.sum_log_div_cube_le_of_two_pow_dvd :
    ∀ (e : ℕ), 1 ≤ e → ∀ S : Finset ℕ, (∀ l ∈ S, (2 ^ (e + 2) : ℤ) ∣ (l : ℤ) - 1 ∨ (2 ^ (e + 2) : ℤ) ∣ (l : ℤ) + 1) →
    ∑ l ∈ S, Real.log l / (l : ℝ) ^ 3 ≤ Real.log ((2 : ℝ) ^ e) / ((2 : ℝ) ^ e) ^ 3 := by
  intro e he S hS
  classical
  set N : ℕ := 2 ^ (e + 2) with hN
  have hN1 : 1 ≤ N := Nat.one_le_two_pow
  have hNR : (N : ℝ) = 4 * (2 : ℝ) ^ e := by rw [hN]; push_cast; ring
  have hn : (2 : ℝ) ≤ 2 ^ e := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := pow_le_pow_right₀ (by norm_num) he
  set f : ℕ → ℝ := fun l => Real.log l / (l : ℝ) ^ 3 with hf
  have hf0 : ∀ l, 0 ≤ f l := fun l => div_nonneg (Real.log_natCast_nonneg l) (by positivity)
  set c : ℝ := Real.log ((2 : ℝ) ^ e) / ((2 : ℝ) ^ e) ^ 3 with hc
  have hc0 : 0 ≤ c := div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  set M := S.sup id with hM
  set R := Finset.range (M + 2) with hR
  have hsub : S ⊆ R.image (fun u => N * u + 1) ∪ R.image (fun u => N * u - 1) := by
    intro l hl
    have hlM : l ≤ M := Finset.le_sup (f := id) hl
    have hZ : (2 ^ (e + 2) : ℤ) = (N : ℤ) := by rw [hN]; push_cast; ring
    have hN2 : 2 ≤ N := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (e + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases hS l hl with h | h
    · left
      rw [hZ] at h
      have hl1 : 1 ≤ l := by
        rcases Nat.eq_zero_or_pos l with rfl | h0
        · exfalso
          have h' : (N : ℤ) ∣ 1 := by simpa using h
          have := Int.le_of_dvd (by norm_num) h'
          omega
        · exact h0
      have h' : N ∣ l - 1 := by
        rw [← Int.natCast_dvd_natCast, Nat.cast_sub hl1]; simpa using h
      obtain ⟨u, hu⟩ := h'
      refine ⟨u, ?_, by omega⟩
      have : u ≤ N * u := Nat.le_mul_of_pos_left u hN1
      rw [hR, Finset.mem_range]; omega
    · right
      rw [hZ] at h
      have h' : N ∣ l + 1 := by
        rw [← Int.natCast_dvd_natCast]; simpa using h
      obtain ⟨u, hu⟩ := h'
      refine ⟨u, ?_, by omega⟩
      have : u ≤ N * u := Nat.le_mul_of_pos_left u hN1
      rw [hR, Finset.mem_range]; omega
  have hb : ∑ u ∈ R, c * (1 / 4 * (1 / (u : ℝ) ^ 2)) ≤ c / 2 := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := sum_inv_sq_range_le M
    have h2 : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
    have h3 : 1 / 4 * ∑ u ∈ R, (1 / (u : ℝ) ^ 2) ≤ 1 / 2 := by rw [hR]; linarith
    nlinarith
  have hA : ∑ l ∈ R.image (fun u => N * u + 1), f l ≤ c / 2 := by
    refine (Finset.sum_image_le_of_nonneg (fun l _ => hf0 l)).trans (le_trans ?_ hb)
    refine Finset.sum_le_sum fun u _ => ?_
    rcases Nat.eq_zero_or_pos u with rfl | h0
    · simp [hf]
    · refine log_div_cube_le_scaled _ _ _ hn (by exact_mod_cast h0) ?_
      push_cast; rw [hNR]; linarith
  have hB : ∑ l ∈ R.image (fun u => N * u - 1), f l ≤ c / 2 := by
    refine (Finset.sum_image_le_of_nonneg (fun l _ => hf0 l)).trans (le_trans ?_ hb)
    refine Finset.sum_le_sum fun u _ => ?_
    rcases Nat.eq_zero_or_pos u with rfl | h0
    · simp [hf]
    · refine log_div_cube_le_scaled _ _ _ hn (by exact_mod_cast h0) ?_
      have : 1 ≤ N * u := Nat.mul_pos hN1 h0
      rw [Nat.cast_sub this]
      push_cast; rw [hNR]
  have h1 : ∑ l ∈ S, f l ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _ => hf0 l)
  have h2 := Finset.sum_union_inter (s₁ := R.image (fun u => N * u + 1)) (s₂ := R.image (fun u => N * u - 1)) (f := f)
  have h3 : 0 ≤ ∑ l ∈ R.image (fun u => N * u + 1) ∩ R.image (fun u => N * u - 1), f l :=
    Finset.sum_nonneg fun l _ => hf0 l
  linarith
