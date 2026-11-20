import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

open Formalism.ConjugateSelfDual Polynomial

namespace UpperTheory.V.Sd

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

/- English proof (translation)
Rewrite using `[sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))`.
-/
private lemma nsub_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))

/- English proof (translation)
The claim follows from `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)`.
-/
private lemma nadd_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

/- English proof (translation)
Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [ha]; exact hb.ne'), ha]`. Conclude with `max_eq_left hb.le`.
-/
private lemma nadd_eq {a b : K} (ha : ‖a‖ = 1) (hb : ‖b‖ < 1) : ‖a + b‖ = 1 := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [ha]; exact hb.ne'), ha]
  exact max_eq_left hb.le

/- English proof (translation)
Establish `h : ‖x‖ ^ N = 1` using `by rw [← norm_pow, hx, norm_one]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg x) hN.ne').1 h`.
-/
private lemma norm_root {N : ℕ} (hN : 0 < N) {x : K} (hx : x ^ N = 1) : ‖x‖ = 1 := by
  have h : ‖x‖ ^ N = 1 := by rw [← norm_pow, hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hN.ne').1 h

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Establish `: 1 - x ^ (i + 1) = (1 - x) + x * (1 - x ^ i)` using `by ring`. Rewrite using `[this]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, hx, one_mul]`. Conclude with `ih`.
-/
private lemma norm_one_sub_pow_le {x : K} (hx : ‖x‖ = 1) (i : ℕ) : ‖1 - x ^ i‖ ≤ ‖1 - x‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have : 1 - x ^ (i + 1) = (1 - x) + x * (1 - x ^ i) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
    rw [norm_mul, hx, one_mul]; exact ih

/- English proof (translation)
Establish `hx1` using `norm_root hN hx`. Use `le_antisymm (nsub_le (by simp) hx1.le) ?_` and prove the remaining obligations. Establish `hs : ∑ i ∈ Finset.range N, x ^ i = 0`. Use `mul_geom_sum x N` as an intermediate fact. Rewrite `this` using `[hx, sub_self]`.

Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)`. Establish `hN' : (N : K) = ∑ i ∈ Finset.range N, (1 - x ^ i)`. Rewrite using `[Finset.sum_sub_distrib, hs]`. Simplify using the standard rewrite rules. Rewrite using `[← hn, hN']`.

Conclude with `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => norm_one_sub_pow_le hx1 i`.
-/
private lemma norm_one_sub {N : ℕ} (hN : 0 < N) (hn : ‖(N : K)‖ = 1) {x : K} (hx : x ^ N = 1) (h1 : x ≠ 1) :
    ‖1 - x‖ = 1 := by
  have hx1 := norm_root hN hx
  refine le_antisymm (nsub_le (by simp) hx1.le) ?_
  have hs : ∑ i ∈ Finset.range N, x ^ i = 0 := by
    have := mul_geom_sum x N
    rw [hx, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)
  have hN' : (N : K) = ∑ i ∈ Finset.range N, (1 - x ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [← hn, hN']
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    fun i _ => norm_one_sub_pow_le hx1 i

/- English proof (translation)
Proceed by induction on `p using Polynomial.induction_on' with`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `nadd_le hp hq`. Consider the case `monomial n a`. Rewrite using `[aeval_monomial, norm_mul, norm_pow]`.

Establish `h1 : ‖algebraMap ℤ K a‖ ≤ 1`. Rewrite using `[eq_intCast]`. Conclude with `IsUltrametricDist.norm_intCast_le_one K a`. Conclude with `mul_le_one₀ h1 (by positivity) (pow_le_one₀ (norm_nonneg _) hx)`.
-/
private lemma norm_aeval_le {x : K} (hx : ‖x‖ ≤ 1) (p : ℤ[X]) : ‖aeval x p‖ ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact nadd_le hp hq
  | monomial n a =>
    rw [aeval_monomial, norm_mul, norm_pow]
    have h1 : ‖algebraMap ℤ K a‖ ≤ 1 := by
      rw [eq_intCast]; exact IsUltrametricDist.norm_intCast_le_one K a
    exact mul_le_one₀ h1 (by positivity) (pow_le_one₀ (norm_nonneg _) hx)

end

/- English proof (translation)
Simplify using `only [numL]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma eulerian_numerator_three : numL 3 = X * (1 + X) := by
  simp only [numL]; simp; ring

/- English proof (translation)
Establish `: numL 4 = X * (derivative (numL 3) * (1 - X) + C (((2 : ℕ) : ℤ) + 1) * numL 3)` using `rfl`. Rewrite using `[this, eulerian_numerator_three]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma eulerian_numerator_four : numL 4 = X * (1 + 4 * X + X ^ 2) := by
  have : numL 4 = X * (derivative (numL 3) * (1 - X) + C (((2 : ℕ) : ℤ) + 1) * numL 3) := rfl
  rw [this, eulerian_numerator_three]; simp; ring

/- English proof (translation)
Establish `: numL 5 = X * (derivative (numL 4) * (1 - X) + C (((3 : ℕ) : ℤ) + 1) * numL 4)` using `rfl`. Rewrite using `[this, eulerian_numerator_four]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma eulerian_numerator_five : numL 5 = X * (1 + X) * (1 + 10 * X + X ^ 2) := by
  have : numL 5 = X * (derivative (numL 4) * (1 - X) + C (((3 : ℕ) : ℤ) + 1) * numL 4) := rfl
  rw [this, eulerian_numerator_four]; simp; ring

section
variable {K : Type} [Field K]

/- English proof (translation)
Simplify using `[Lk, eulerian_numerator_three]`.
-/
private lemma eulerian_three_eq (x : K) : Lk 3 x = x * (1 + x) / (1 - x) ^ 3 := by
  simp [Lk, eulerian_numerator_three]

/- English proof (translation)
Establish `: Lk 4 x = x * (1 + 4 * x + x ^ 2) / (1 - x) ^ 4`. Simplify using `[Lk, eulerian_numerator_four, map_ofNat]`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma eulerian_four_eq {x : K} (h : 1 - x ≠ 0) :
    Lk 4 x = (x / (1 - x) ^ 2) * (1 + 6 * (x / (1 - x) ^ 2)) := by
  have : Lk 4 x = x * (1 + 4 * x + x ^ 2) / (1 - x) ^ 4 := by
    simp [Lk, eulerian_numerator_four, map_ofNat]
  rw [this]; field_simp; ring

/- English proof (translation)
Establish `: Lk 5 x = x * (1 + x) * (1 + 10 * x + x ^ 2) / (1 - x) ^ 5`. Simplify using `[Lk, eulerian_numerator_five, map_ofNat]`. Rewrite using `[this, eulerian_three_eq]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma eulerian_five_eq {x : K} (h : 1 - x ≠ 0) :
    Lk 5 x = Lk 3 x * (1 + 12 * (x / (1 - x) ^ 2)) := by
  have : Lk 5 x = x * (1 + x) * (1 + 10 * x + x ^ 2) / (1 - x) ^ 5 := by
    simp [Lk, eulerian_numerator_five, map_ofNat]
  rw [this, eulerian_three_eq]; field_simp; ring

end

/- English proof (translation)
Establish `h1 : (N : Qbar l) = algebraMap ℚ_[l] (Qbar l) (N : ℚ_[l])` using `by simp`. Rewrite using `[h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]`. Conclude with `(Nat.Prime.coprime_iff_not_dvd Fact.out).2 h`.
-/
private lemma norm_nat {l : ℕ} [Fact l.Prime] {N : ℕ} (h : ¬ l ∣ N) : ‖(N : Qbar l)‖ = 1 := by
  have h1 : (N : Qbar l) = algebraMap ℚ_[l] (Qbar l) (N : ℚ_[l]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 h

/- English proof (translation)
Establish `h1 : (N : Qbar l) = algebraMap ℚ_[l] (Qbar l) (N : ℚ_[l])` using `by simp`. Rewrite using `[h1, norm_algebraMap', Padic.norm_natCast_lt_one_iff]`. Conclude with `h`.
-/
private lemma norm_nat_lt {l : ℕ} [Fact l.Prime] {N : ℕ} (h : l ∣ N) : ‖(N : Qbar l)‖ < 1 := by
  have h1 : (N : Qbar l) = algebraMap ℚ_[l] (Qbar l) (N : ℚ_[l]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_lt_one_iff]
  exact h

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
/- English proof (translation)
Introduce `l _ hl2 N hN hlN`. Establish `hn : ‖(N : Qbar l)‖ = 1` using `norm_nat hlN`. Establish `h1 : ∀ (k : ℕ) (x : Qbar l), x ^ N = 1 → x ≠ 1 → ‖Lk k x‖ ≤ 1`. Introduce `k x hx h`. Rewrite using `[Lk, norm_div, norm_pow, norm_one_sub hN hn hx h, one_pow, div_one]`.

Conclude with `norm_aeval_le (norm_root hN hx).le _`. Establish `hne : ∀ x : Qbar l, x ^ 2 ≠ 1 → x ≠ 1`. Introduce and unpack `x h rfl`. Conclude with `h (one_pow 2)`. Establish `h3 : ∀ x : Qbar l, x ^ N = 1 → x ^ 2 ≠ 1 → ‖Lk 3 x‖ = 1`.

Introduce `x hx h`. Establish `ha` using `norm_one_sub hN hn hx (hne x h)`. Establish `hb : ‖1 - x ^ 2‖ = 1` using `norm_one_sub hN hn (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) h`. Establish `hc : ‖1 + x‖ = 1`. Establish `: 1 - x ^ 2 = (1 - x) * (1 + x)` using `by ring`.

Rewrite `hb` using `[this, norm_mul, ha, one_mul]`. Then use the resulting hypothesis. Rewrite using `[eulerian_three_eq, norm_div, norm_mul, norm_pow, ha, hc, norm_root hN hx]`. Evaluate the numerical expressions. Use `⟨h1, h3, ?_⟩` and prove the remaining obligations. Introduce `x y hx hy hx2 hy2 hyx hyx'`.

Establish `hax` using `norm_one_sub hN hn hx (hne x hx2)`. Establish `hay` using `norm_one_sub hN hn hy (hne y hy2)`. Establish `hnx` using `norm_root hN hx`. Establish `hny` using `norm_root hN hy`. Establish `hx0 : x ≠ 0` using `by rintro rfl; simp at hnx`.

Establish `hx1 : 1 - x ≠ 0` using `sub_ne_zero.2 (hne x hx2).symm`. Establish `hy1 : 1 - y ≠ 0` using `sub_ne_zero.2 (hne y hy2).symm`. Establish `hxy : ‖1 - x * y‖ = 1`. Use `norm_one_sub hN hn (by rw [mul_pow, hx, hy, one_mul]) fun h => hyx' ?_` and prove the remaining obligations. Conclude with `eq_inv_of_mul_eq_one_right h`.

Establish `hxy' : ‖1 - y / x‖ = 1`. Use `norm_one_sub hN hn (by rw [div_pow, hx, hy, div_one]) fun h => hyx ?_` and prove the remaining obligations. Conclude with `(div_eq_one_iff_eq hx0).1 h`. Establish `h4x` using `eulerian_four_eq hx1`. Establish `h4y` using `eulerian_four_eq hy1`.

Establish `h5x` using `eulerian_five_eq hx1`. Establish `h5y` using `eulerian_five_eq hy1`. Establish `hu : ‖x / (1 - x) ^ 2‖ = 1` using `by rw [norm_div, norm_pow, hax, hnx]; norm_num`. Establish `hv : ‖y / (1 - y) ^ 2‖ = 1` using `by rw [norm_div, norm_pow, hay, hny]; norm_num`. Establish `huv : ‖x / (1 - x) ^ 2 - y / (1 - y) ^ 2‖ = 1`.

Establish `: x / (1 - x) ^ 2 - y / (1 - y) ^ 2 = x * (1 - y / x) * (1 - x * y) / ((1 - x) ^ 2 * (1 - y) ^ 2)` using `by field_simp; ring`. Rewrite using `[this, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, hax, hay, hnx, hxy, hxy']`. Evaluate the numerical expressions. Generalize the expression as in `x / (1 - x) ^ 2 = u at *`. Generalize the expression as in `y / (1 - y) ^ 2 = v at *`.

Distinguish the cases in `h6 : l ∣ 6`. Use `left`. Establish `h6' : ‖(6 : Qbar l)‖ < 1` using `by exact_mod_cast norm_nat_lt h6`. Establish `: Lk 4 x - Lk 4 y = (u - v) * (1 + 6 * (u + v))` using `by rw [h4x, h4y]; ring`. Rewrite using `[this, norm_mul, huv, one_mul]`.

Use `nadd_eq norm_one ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h6' (nadd_le hu.le hv.le)`. Use `right`. Establish `h12 : ¬ l ∣ 12`.

Introduce `h`. Establish `hp : l.Prime` using `Fact.out`. Establish `h' : l ∣ 6 ^ 2` using `h.trans (by norm_num)`. Conclude with `h6 (hp.dvd_of_dvd_pow h')`. Establish `h12' : ‖(12 : Qbar l)‖ = 1` using `by exact_mod_cast norm_nat h12`.

Establish `hA` using `h3 x hx hx2`. Establish `hB` using `h3 y hy hy2`. Establish `hle : ‖Lk 3 x ^ 2 - Lk 3 y ^ 2‖ ≤ 1` using `nsub_le (by rw [norm_pow, hA]; norm_num) (by rw [norm_pow, hB]; norm_num)`. Break down `hle.eq_or_lt with h | h` into its components or cases. Conclude with `Or.inl h`.

Use `right`. Establish `: Lk 3 x * Lk 5 x - Lk 3 y * Lk 5 y = 12 * Lk 3 x ^ 2 * (u - v) + (Lk 3 x ^ 2 - Lk 3 y ^ 2) * (1 + 12 * v)`. Rewrite using `[h5x, h5y]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Use `nadd_eq (by rw [norm_mul, norm_mul, norm_pow, h12', hA, huv]; norm_num) ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h (nadd_le norm_one.le (by rw [norm_mul, h12', hv]; norm_num))`.
-/
theorem UpperTheory.V.Sd.lkSep :
    UpperTheory.V.Sd.LkSep := by
  intro l _ hl2 N hN hlN
  have hn : ‖(N : Qbar l)‖ = 1 := norm_nat hlN
  have h1 : ∀ (k : ℕ) (x : Qbar l), x ^ N = 1 → x ≠ 1 → ‖Lk k x‖ ≤ 1 := by
    intro k x hx h
    rw [Lk, norm_div, norm_pow, norm_one_sub hN hn hx h, one_pow, div_one]
    exact norm_aeval_le (norm_root hN hx).le _
  have hne : ∀ x : Qbar l, x ^ 2 ≠ 1 → x ≠ 1 := by
    rintro x h rfl; exact h (one_pow 2)
  have h3 : ∀ x : Qbar l, x ^ N = 1 → x ^ 2 ≠ 1 → ‖Lk 3 x‖ = 1 := by
    intro x hx h
    have ha := norm_one_sub hN hn hx (hne x h)
    have hb : ‖1 - x ^ 2‖ = 1 :=
      norm_one_sub hN hn (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) h
    have hc : ‖1 + x‖ = 1 := by
      have : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
      rwa [this, norm_mul, ha, one_mul] at hb
    rw [eulerian_three_eq, norm_div, norm_mul, norm_pow, ha, hc, norm_root hN hx]; norm_num
  refine ⟨h1, h3, ?_⟩
  intro x y hx hy hx2 hy2 hyx hyx'
  have hax := norm_one_sub hN hn hx (hne x hx2)
  have hay := norm_one_sub hN hn hy (hne y hy2)
  have hnx := norm_root hN hx
  have hny := norm_root hN hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at hnx
  have hx1 : 1 - x ≠ 0 := sub_ne_zero.2 (hne x hx2).symm
  have hy1 : 1 - y ≠ 0 := sub_ne_zero.2 (hne y hy2).symm
  have hxy : ‖1 - x * y‖ = 1 := by
    refine norm_one_sub hN hn (by rw [mul_pow, hx, hy, one_mul]) fun h => hyx' ?_
    exact eq_inv_of_mul_eq_one_right h
  have hxy' : ‖1 - y / x‖ = 1 := by
    refine norm_one_sub hN hn (by rw [div_pow, hx, hy, div_one]) fun h => hyx ?_
    exact (div_eq_one_iff_eq hx0).1 h
  have h4x := eulerian_four_eq hx1
  have h4y := eulerian_four_eq hy1
  have h5x := eulerian_five_eq hx1
  have h5y := eulerian_five_eq hy1
  have hu : ‖x / (1 - x) ^ 2‖ = 1 := by rw [norm_div, norm_pow, hax, hnx]; norm_num
  have hv : ‖y / (1 - y) ^ 2‖ = 1 := by rw [norm_div, norm_pow, hay, hny]; norm_num
  have huv : ‖x / (1 - x) ^ 2 - y / (1 - y) ^ 2‖ = 1 := by
    have : x / (1 - x) ^ 2 - y / (1 - y) ^ 2
        = x * (1 - y / x) * (1 - x * y) / ((1 - x) ^ 2 * (1 - y) ^ 2) := by
      field_simp; ring
    rw [this, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, hax, hay, hnx, hxy, hxy']
    norm_num
  generalize x / (1 - x) ^ 2 = u at *
  generalize y / (1 - y) ^ 2 = v at *
  by_cases h6 : l ∣ 6
  · left
    have h6' : ‖(6 : Qbar l)‖ < 1 := by exact_mod_cast norm_nat_lt h6
    have : Lk 4 x - Lk 4 y = (u - v) * (1 + 6 * (u + v)) := by rw [h4x, h4y]; ring
    rw [this, norm_mul, huv, one_mul]
    refine nadd_eq norm_one ?_
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h6' (nadd_le hu.le hv.le)
  · right
    have h12 : ¬ l ∣ 12 := by
      intro h
      have hp : l.Prime := Fact.out
      have h' : l ∣ 6 ^ 2 := h.trans (by norm_num)
      exact h6 (hp.dvd_of_dvd_pow h')
    have h12' : ‖(12 : Qbar l)‖ = 1 := by exact_mod_cast norm_nat h12
    have hA := h3 x hx hx2
    have hB := h3 y hy hy2
    have hle : ‖Lk 3 x ^ 2 - Lk 3 y ^ 2‖ ≤ 1 :=
      nsub_le (by rw [norm_pow, hA]; norm_num) (by rw [norm_pow, hB]; norm_num)
    rcases hle.eq_or_lt with h | h
    · exact Or.inl h
    · right
      have : Lk 3 x * Lk 5 x - Lk 3 y * Lk 5 y
          = 12 * Lk 3 x ^ 2 * (u - v) + (Lk 3 x ^ 2 - Lk 3 y ^ 2) * (1 + 12 * v) := by
        rw [h5x, h5y]; ring
      rw [this]
      refine nadd_eq (by rw [norm_mul, norm_mul, norm_pow, h12', hA, huv]; norm_num) ?_
      rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h
        (nadd_le norm_one.le (by rw [norm_mul, h12', hv]; norm_num))
