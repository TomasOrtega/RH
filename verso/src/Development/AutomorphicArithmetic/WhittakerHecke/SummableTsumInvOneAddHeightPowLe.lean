import Mathlib

/- English proof (translation)
Establish `hinj' : Function.Injective (fun x : R => τ x.1)`. Introduce `a b h`. Conclude with `Subtype.ext (hinj a.2 b.2 h)`. Establish `hs : Summable (fun x : R => w (τ x.1))` using `hw.comp_injective hinj'`. Establish `hs2 : Summable (fun x : R => f x.1)` using `Summable.of_nonneg_of_le (fun x => hf _) (fun x => hb x.1 x.2) (hs.mul_left K)`.

Use `⟨summable_subtype_iff_indicator.mp hs2, ?_⟩` and prove the remaining obligations. Rewrite using `[← tsum_subtype R f]`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ hK` to reduce the goal to its premises. Conclude with `Summable.tsum_le_tsum_of_inj _ hinj' (fun c _ => hw0 c) (fun _ => le_rfl) hs hw`.
-/
private lemma gen {ι : Type*} (R : Set ι) (f : ι → ℝ) (hf : ∀ x, 0 ≤ f x) (τ : ι → ℤ × ℤ)
    (hinj : Set.InjOn τ R) (w : ℤ × ℤ → ℝ) (hw : Summable w) (hw0 : ∀ x, 0 ≤ w x)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ x ∈ R, f x ≤ K * w (τ x)) :
    Summable (R.indicator f) ∧ ∑' x, R.indicator f x ≤ K * ∑' x, w x := by
  classical
  have hinj' : Function.Injective (fun x : R => τ x.1) := by
    intro a b h
    exact Subtype.ext (hinj a.2 b.2 h)
  have hs : Summable (fun x : R => w (τ x.1)) := hw.comp_injective hinj'
  have hs2 : Summable (fun x : R => f x.1) :=
    Summable.of_nonneg_of_le (fun x => hf _) (fun x => hb x.1 x.2) (hs.mul_left K)
  refine ⟨summable_subtype_iff_indicator.mp hs2, ?_⟩
  rw [← tsum_subtype R f]
  calc ∑' x : R, f x.1 ≤ ∑' x : R, K * w (τ x.1) :=
        hs2.tsum_le_tsum (fun x => hb x.1 x.2) (hs.mul_left K)
    _ = K * ∑' x : R, w (τ x.1) := tsum_mul_left
    _ ≤ K * ∑' x, w x := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact Summable.tsum_le_tsum_of_inj _ hinj' (fun c _ => hw0 c) (fun _ => le_rfl) hs hw

/- English proof (translation)
Establish `h0 : Summable (fun m : ℕ => ((1 + (m : ℝ)) ^ 2)⁻¹)`. Establish `h` using `(Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)`. Establish `h'` using `(summable_nat_add_iff 1).mpr h`. Use `h'.congr (fun m => ?_)` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[one_div, add_comm]`. Apply `Summable.of_nat_of_neg` to reduce the goal to its premises. Use `h0.congr (fun m => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `h0.congr (fun m => ?_)` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
private lemma wsum1 : Summable (fun l : ℤ => ((1 + |(l : ℝ)|) ^ 2)⁻¹) := by
  have h0 : Summable (fun m : ℕ => ((1 + (m : ℝ)) ^ 2)⁻¹) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have h' := (summable_nat_add_iff 1).mpr h
    refine h'.congr (fun m => ?_)
    push_cast
    rw [one_div, add_comm]
  apply Summable.of_nat_of_neg
  · refine h0.congr (fun m => ?_)
    simp
  · refine h0.congr (fun m => ?_)
    simp

/- English proof (translation)
The claim follows from `Summable.mul_of_nonneg wsum1 wsum1 (fun _ => by positivity) (fun _ => by positivity)`.
-/
private lemma wsum : Summable (fun p : ℤ × ℤ => ((1 + |(p.1 : ℝ)|) ^ 2)⁻¹ * ((1 + |(p.2 : ℝ)|) ^ 2)⁻¹) :=
  Summable.mul_of_nonneg wsum1 wsum1 (fun _ => by positivity) (fun _ => by positivity)

/- English proof (translation)
Establish `h` using `abs_sub_round x`. Establish `h2 : |((round x : ℤ) : ℝ)| ≤ |x| + |x - round x|`. Use `abs_sub_abs_le_abs_sub ((round x : ℤ) : ℝ) x` as an intermediate fact. Rewrite `this` using `[abs_sub_comm]`. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the linear relations using `[abs_nonneg x]`.
-/
private lemma round_bd (x : ℝ) : 1 + |((round x : ℤ) : ℝ)| ≤ 2 * (1 + |x|) := by
  have h := abs_sub_round x
  have h2 : |((round x : ℤ) : ℝ)| ≤ |x| + |x - round x| := by
    have := abs_sub_abs_le_abs_sub ((round x : ℤ) : ℝ) x
    rw [abs_sub_comm] at this
    linarith
  linarith [abs_nonneg x]

/- English proof (translation)
Establish `hBu0 : 0 < Bu` using `by linarith`. Establish `hα0 : 0 < α` using `lt_of_lt_of_le (inv_pos.mpr hBu0) hα`. Establish `hT0 : 0 < T` using `by linarith`. Establish `hd0 : 0 < d` using `by linarith`. Establish `hδ : κ / (Bu * d) ≤ 1`.

Rewrite using `[div_le_one (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hδ' : κ / (T * d) ≤ 1`. Rewrite using `[div_le_one (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hA : (κ / (Bu * d)) * (1 + d * a) ≤ 1 + κ * (a * α)`. Establish `e : (κ / (Bu * d)) * (1 + d * a) = κ / (Bu * d) + κ * (a * Bu⁻¹)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Establish `: κ * (a * Bu⁻¹) ≤ κ * (a * α)` using `by gcongr`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB : (κ / (T * d)) * (1 + d * b) ≤ 1 + κ * (b / α)`. Establish `e : (κ / (T * d)) * (1 + d * b) = κ / (T * d) + κ * (b / T)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Establish `: κ * (b / T) ≤ κ * (b / α)` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hA0 : 0 ≤ κ * (a * α)` using `by positivity`. Establish `hB0 : 0 ≤ κ * (b / α)` using `by positivity`. Establish `hprod : ((κ / (Bu * d)) * (1 + d * a)) * ((κ / (T * d)) * (1 + d * b)) ≤ (1 + κ * (a * α)) * (1 + κ * (b / α))` using `mul_le_mul hA hB (by positivity) (by positivity)`.

Establish `e2 : (1 + κ * ν) = 1 + κ * (a * α) + κ * (b / α)` using `by rw [hν]; ring`. Rewrite using `[e2]`. Use polynomial arithmetic with `[mul_nonneg hA0 hB0]`.
-/
private lemma nu_lower (κ Bu α T d ν a b : ℝ) (hd : 1 ≤ d) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hBu : 1 ≤ Bu)
    (hα : Bu⁻¹ ≤ α) (hαT : α ≤ T) (hT : 1 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hν : ν = a * α + b / α) :
    (κ / (Bu * d)) * (κ / (T * d)) * ((1 + d * a) * (1 + d * b)) ≤ (1 + κ * ν) ^ 2 := by
  have hBu0 : 0 < Bu := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have hδ : κ / (Bu * d) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hδ' : κ / (T * d) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hA : (κ / (Bu * d)) * (1 + d * a) ≤ 1 + κ * (a * α) := by
    have e : (κ / (Bu * d)) * (1 + d * a) = κ / (Bu * d) + κ * (a * Bu⁻¹) := by
      field_simp
    rw [e]
    have : κ * (a * Bu⁻¹) ≤ κ * (a * α) := by gcongr
    linarith
  have hB : (κ / (T * d)) * (1 + d * b) ≤ 1 + κ * (b / α) := by
    have e : (κ / (T * d)) * (1 + d * b) = κ / (T * d) + κ * (b / T) := by
      field_simp
    rw [e]
    have : κ * (b / T) ≤ κ * (b / α) := by gcongr
    linarith
  have hA0 : 0 ≤ κ * (a * α) := by positivity
  have hB0 : 0 ≤ κ * (b / α) := by positivity
  have hprod : ((κ / (Bu * d)) * (1 + d * a)) * ((κ / (T * d)) * (1 + d * b))
      ≤ (1 + κ * (a * α)) * (1 + κ * (b / α)) :=
    mul_le_mul hA hB (by positivity) (by positivity)
  have e2 : (1 + κ * ν) = 1 + κ * (a * α) + κ * (b / α) := by rw [hν]; ring
  rw [e2]
  nlinarith [mul_nonneg hA0 hB0]

/- English proof (translation)
Establish `hBu0 : 0 < Bu` using `by linarith`. Establish `hα0 : 0 < α` using `lt_of_lt_of_le (inv_pos.mpr hBu0) hα`. Establish `hT0 : 0 < T` using `by linarith`. Establish `hd0 : 0 < d` using `by linarith`. Establish `h1 : d⁻¹ ≤ a`.

Rewrite using `[inv_le_iff_one_le_mul₀ hd0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : T⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ hT`. Establish `h3 : Bu⁻¹ * T⁻¹ ≤ α`. Establish `: Bu⁻¹ * T⁻¹ ≤ Bu⁻¹ * 1` using `by gcongr`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : 1 / (d * Bu * T) = d⁻¹ * (Bu⁻¹ * T⁻¹)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`. Establish `: d⁻¹ * (Bu⁻¹ * T⁻¹) ≤ a * α` using `mul_le_mul h1 h3 (by positivity) ha`.

Establish `h4 : 0 ≤ b / α` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma lower_bound_first_case (d Bu T α a b : ℝ) (hd : 1 ≤ d) (hBu : 1 ≤ Bu) (hα : Bu⁻¹ ≤ α) (hT : 1 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 1 ≤ d * a) : 1 / (d * Bu * T) ≤ a * α + b / α := by
  have hBu0 : 0 < Bu := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have h1 : d⁻¹ ≤ a := by
    rw [inv_le_iff_one_le_mul₀ hd0]; linarith
  have h2 : T⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hT
  have h3 : Bu⁻¹ * T⁻¹ ≤ α := by
    have : Bu⁻¹ * T⁻¹ ≤ Bu⁻¹ * 1 := by gcongr
    linarith
  have e : 1 / (d * Bu * T) = d⁻¹ * (Bu⁻¹ * T⁻¹) := by
    field_simp
  rw [e]
  have : d⁻¹ * (Bu⁻¹ * T⁻¹) ≤ a * α := mul_le_mul h1 h3 (by positivity) ha
  have h4 : 0 ≤ b / α := by positivity
  linarith

/- English proof (translation)
Establish `hBu0 : 0 < Bu` using `by linarith`. Establish `hα0 : 0 < α` using `lt_of_lt_of_le (inv_pos.mpr hBu0) hα`. Establish `hT0 : 0 < T` using `by linarith`. Establish `hd0 : 0 < d` using `by linarith`. Establish `h1 : d⁻¹ ≤ b`.

Rewrite using `[inv_le_iff_one_le_mul₀ hd0]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : Bu⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ hBu`. Establish `h3 : T⁻¹ ≤ α⁻¹` using `inv_anti₀ hα0 hαT`. Establish `h5 : Bu⁻¹ * T⁻¹ ≤ α⁻¹`.

Establish `: Bu⁻¹ * T⁻¹ ≤ 1 * T⁻¹` using `by gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e : 1 / (d * Bu * T) = d⁻¹ * (Bu⁻¹ * T⁻¹)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e, div_eq_mul_inv]`.

Establish `: d⁻¹ * (Bu⁻¹ * T⁻¹) ≤ b * α⁻¹` using `mul_le_mul h1 h5 (by positivity) hb`. Establish `h4 : 0 ≤ a * α` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma lower_bound_second_case (d Bu T α a b : ℝ) (hd : 1 ≤ d) (hBu : 1 ≤ Bu) (hα : Bu⁻¹ ≤ α) (hαT : α ≤ T)
    (hT : 1 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : 1 ≤ d * b) : 1 / (d * Bu * T) ≤ a * α + b / α := by
  have hBu0 : 0 < Bu := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have h1 : d⁻¹ ≤ b := by
    rw [inv_le_iff_one_le_mul₀ hd0]; linarith
  have h2 : Bu⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hBu
  have h3 : T⁻¹ ≤ α⁻¹ := inv_anti₀ hα0 hαT
  have h5 : Bu⁻¹ * T⁻¹ ≤ α⁻¹ := by
    have : Bu⁻¹ * T⁻¹ ≤ 1 * T⁻¹ := by gcongr
    linarith
  have e : 1 / (d * Bu * T) = d⁻¹ * (Bu⁻¹ * T⁻¹) := by
    field_simp
  rw [e, div_eq_mul_inv]
  have : d⁻¹ * (Bu⁻¹ * T⁻¹) ≤ b * α⁻¹ := mul_le_mul h1 h5 (by positivity) hb
  have h4 : 0 ≤ a * α := by positivity
  linarith

/- English proof (translation)
Establish `hBu0 : 0 < Bu` using `by linarith`. Establish `hα0 : 0 < α` using `lt_of_lt_of_le (inv_pos.mpr hBu0) hα`. Establish `hT0 : 0 < T` using `by linarith`. Establish `hd0 : 0 < d` using `by linarith`. Establish `hν0 : 0 ≤ ν` using `by rw [hν]; positivity`.

Establish `hE1 : 1 ≤ Real.exp t` using `Real.one_le_exp ht`. Use `set E := Real.exp t with hE`. Establish `hE0 : 0 < E` using `by linarith`. Establish `hlow` using `nu_lower κ Bu α T d ν a b hd hκ hκ1 hBu hα hαT hT ha hb hν`. Use `set X := 1 + κ * E * ν with hX`.

Establish `hX1 : κ * E * (1 / (d * Bu * T)) ≤ X`. Establish `: κ * E * (1 / (d * Bu * T)) ≤ κ * E * ν` using `by gcongr`. Establish `h0 : 0 ≤ κ * E * ν` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX2 : 1 + κ * ν ≤ X`.

Establish `: κ * ν ≤ κ * E * ν`. Establish `: κ * 1 ≤ κ * E` using `by gcongr`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hQ : (1 + L) * (1 + M) ≤ 4 * ((1 + d * a) * (1 + d * b))`.

Use `mul_le_mul hL hM (by positivity) (by positivity)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Use `set c1 := κ / (Bu * d) with hc1`. Use `set c2 := κ / (T * d) with hc2`. Establish `hc10 : 0 < c1` using `by positivity`.

Establish `hc20 : 0 < c2` using `by positivity`. Establish `hY : (c1 * c2 / 4) * ((1 + L) * (1 + M)) ≤ (1 + κ * ν) ^ 2`. Establish `h1 : c1 * c2 * ((1 + L) * (1 + M)) ≤ c1 * c2 * (4 * ((1 + d * a) * (1 + d * b)))` using `by gcongr`. Use the polynomial consequences of the given equalities and inequalities. Establish `hY0 : 0 < (c1 * c2 / 4) * ((1 + L) * (1 + M))` using `by positivity`.

Establish `hX4 : ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2 ≤ X ^ 4`. Combine the equalities or inequalities in the displayed calculation. Establish `: 0 ≤ 1 + κ * ν` using `by positivity`. Use `gcongr`. Establish `hXn : (κ * E * (1 / (d * Bu * T))) ^ n ≤ X ^ n` using `by gcongr`.

Establish `hmain : (κ * E * (1 / (d * Bu * T))) ^ n * ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2 ≤ X ^ (n + 4)`. Rewrite using `[pow_add]`. Conclude with `mul_le_mul hXn hX4 (by positivity) (by positivity)`. Establish `hpos : 0 < (κ * E * (1 / (d * Bu * T))) ^ n * ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2`. Check the signs of the components of the expression.

Use `(inv_anti₀ hpos hmain).trans (le_of_eq ?_)` and prove the remaining obligations. Establish `hexp : Real.exp (-((n : ℝ) * t)) = (E ^ n)⁻¹`. Rewrite using `[Real.exp_neg, Real.exp_nat_mul]`. Rewrite using `[hexp, hc1, hc2, pow_add T n 2]`. Establish `e1 : κ * E * (1 / (d * Bu * T)) = (κ / (d * Bu)) * E * T⁻¹`.

Clear the denominators using the available nonvanishing facts. Establish `e2 : d * Bu / κ = (κ / (d * Bu))⁻¹`. Rewrite using `[inv_div]`. Rewrite using `[e1, e2, mul_pow, mul_pow, inv_pow, inv_pow]`. Establish `hu : κ / (d * Bu) ≠ 0` using `by positivity`.

Establish `hun : (κ / (d * Bu)) ^ n ≠ 0` using `pow_ne_zero _ hu`. Establish `hEn : E ^ n ≠ 0` using `pow_ne_zero _ hE0.ne'`. Establish `hTn : T ^ n ≠ 0` using `pow_ne_zero _ hT0.ne'`. Generalize the expression as in `(κ / (d * Bu)) ^ n = U at *`. Generalize the expression as in `E ^ n = V at *`.

Generalize the expression as in `T ^ n = W' at *`. Establish `hL1 : 1 + L ≠ 0` using `by positivity`. Establish `hM1 : 1 + M ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma term_bd (n : ℕ) (κ Bu α T d ν a b t L M : ℝ) (hd : 1 ≤ d) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hBu : 1 ≤ Bu) (hα : Bu⁻¹ ≤ α) (hαT : α ≤ T) (hT : 1 ≤ T) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht : 0 ≤ t) (hν : ν = a * α + b / α) (hν1 : 1 / (d * Bu * T) ≤ ν) (hL0 : 0 ≤ L) (hM0 : 0 ≤ M)
    (hL : 1 + L ≤ 2 * (1 + d * a)) (hM : 1 + M ≤ 2 * (1 + d * b)) :
    ((1 + κ * Real.exp t * ν) ^ (n + 4))⁻¹ ≤
      (16 * (d * Bu / κ) ^ n * ((d / κ) * (Bu * d / κ)) ^ 2) * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2) *
        (((1 + L) ^ 2)⁻¹ * ((1 + M) ^ 2)⁻¹) := by
  have hBu0 : 0 < Bu := by linarith
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  have hd0 : 0 < d := by linarith
  have hν0 : 0 ≤ ν := by rw [hν]; positivity
  have hE1 : 1 ≤ Real.exp t := Real.one_le_exp ht
  set E := Real.exp t with hE
  have hE0 : 0 < E := by linarith
  have hlow := nu_lower κ Bu α T d ν a b hd hκ hκ1 hBu hα hαT hT ha hb hν
  set X := 1 + κ * E * ν with hX
  have hX1 : κ * E * (1 / (d * Bu * T)) ≤ X := by
    have : κ * E * (1 / (d * Bu * T)) ≤ κ * E * ν := by gcongr
    have h0 : 0 ≤ κ * E * ν := by positivity
    linarith
  have hX2 : 1 + κ * ν ≤ X := by
    have : κ * ν ≤ κ * E * ν := by
      have : κ * 1 ≤ κ * E := by gcongr
      nlinarith
    linarith
  have hQ : (1 + L) * (1 + M) ≤ 4 * ((1 + d * a) * (1 + d * b)) := by
    have := mul_le_mul hL hM (by positivity) (by positivity)
    nlinarith
  set c1 := κ / (Bu * d) with hc1
  set c2 := κ / (T * d) with hc2
  have hc10 : 0 < c1 := by positivity
  have hc20 : 0 < c2 := by positivity
  have hY : (c1 * c2 / 4) * ((1 + L) * (1 + M)) ≤ (1 + κ * ν) ^ 2 := by
    have h1 : c1 * c2 * ((1 + L) * (1 + M)) ≤ c1 * c2 * (4 * ((1 + d * a) * (1 + d * b))) := by gcongr
    nlinarith
  have hY0 : 0 < (c1 * c2 / 4) * ((1 + L) * (1 + M)) := by positivity
  have hX4 : ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2 ≤ X ^ 4 := by
    calc ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2 ≤ ((1 + κ * ν) ^ 2) ^ 2 := by gcongr
      _ = (1 + κ * ν) ^ 4 := by ring
      _ ≤ X ^ 4 := by
        have : 0 ≤ 1 + κ * ν := by positivity
        gcongr
  have hXn : (κ * E * (1 / (d * Bu * T))) ^ n ≤ X ^ n := by gcongr
  have hmain : (κ * E * (1 / (d * Bu * T))) ^ n * ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2
      ≤ X ^ (n + 4) := by
    rw [pow_add]
    exact mul_le_mul hXn hX4 (by positivity) (by positivity)
  have hpos : 0 < (κ * E * (1 / (d * Bu * T))) ^ n * ((c1 * c2 / 4) * ((1 + L) * (1 + M))) ^ 2 := by
    positivity
  refine (inv_anti₀ hpos hmain).trans (le_of_eq ?_)
  have hexp : Real.exp (-((n : ℝ) * t)) = (E ^ n)⁻¹ := by
    rw [Real.exp_neg, Real.exp_nat_mul]
  rw [hexp, hc1, hc2, pow_add T n 2]
  have e1 : κ * E * (1 / (d * Bu * T)) = (κ / (d * Bu)) * E * T⁻¹ := by
    field_simp
  have e2 : d * Bu / κ = (κ / (d * Bu))⁻¹ := by
    rw [inv_div]
  rw [e1, e2, mul_pow, mul_pow, inv_pow, inv_pow]
  have hu : κ / (d * Bu) ≠ 0 := by positivity
  have hun : (κ / (d * Bu)) ^ n ≠ 0 := pow_ne_zero _ hu
  have hEn : E ^ n ≠ 0 := pow_ne_zero _ hE0.ne'
  have hTn : T ^ n ≠ 0 := pow_ne_zero _ hT0.ne'
  generalize (κ / (d * Bu)) ^ n = U at *
  generalize E ^ n = V at *
  generalize T ^ n = W' at *
  have hL1 : 1 + L ≠ 0 := by positivity
  have hM1 : 1 + M ≠ 0 := by positivity
  field_simp
  ring

/- English proof (translation)
Introduce `n d κ Bu hd hκ hκ1 hBu`. Establish `hd1 : (1 : ℝ) ≤ (d : ℝ)` using `by exact_mod_cast hd`. Establish `hd0 : (0 : ℝ) < (d : ℝ)` using `by linarith`. Establish `hBu0 : 0 < Bu` using `by linarith`. Use `set w : ℤ × ℤ → ℝ := fun p => ((1 + |(p.1 : ℝ)|) ^ 2)⁻¹ * ((1 + |(p.2 : ℝ)|) ^ 2)⁻¹ with hw`.

Establish `hw0 : ∀ p, 0 ≤ w p` using `fun p => by simp only [hw]; positivity`. Use `set C : ℝ := 16 * ((d : ℝ) * Bu / κ) ^ n * (((d : ℝ) / κ) * (Bu * (d : ℝ) / κ)) ^ 2 with hC`. Establish `hC0 : 0 ≤ C` using `by rw [hC]; positivity`. Use `⟨C * ∑' p, w p, mul_nonneg hC0 (tsum_nonneg hw0), ?_⟩` and prove the remaining obligations. Introduce `R β α T t ht hα hαT hT h1 h2 h3`.

Establish `hα0 : 0 < α` using `lt_of_lt_of_le (inv_pos.mpr hBu0) hα`. Establish `hT0 : 0 < T` using `by linarith`. Use `set τ : {r : Fin 2 → ℚ // r ≠ 0} → ℤ × ℤ := fun ξ => (round ((d : ℝ) * ((ξ.1 0 : ℚ) : ℝ)), round ((d : ℝ) * (((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)))) with hτ`. Establish `hinj : Set.InjOn τ R`. Introduce `ξ hξ ξ' hξ' he`.

Establish `he1` using `congrArg Prod.fst he`. Establish `he2` using `congrArg Prod.snd he`. Simplify using `only [hτ] at he1 he2`. Take `⟨l, hl⟩` from `h1 ξ hξ`. Take `⟨l', hl'⟩` from `h1 ξ' hξ'`.

Establish `hlR : (d : ℝ) * ((ξ.1 0 : ℚ) : ℝ) = (l : ℝ)` using `by exact_mod_cast hl`. Establish `hlR' : (d : ℝ) * ((ξ'.1 0 : ℚ) : ℝ) = (l' : ℝ)` using `by exact_mod_cast hl'`. Rewrite `he1` using `[hlR, hlR', round_intCast, round_intCast]`. Establish `h0 : ξ.1 0 = ξ'.1 0`. Establish `: (d : ℚ) * ξ.1 0 = (d : ℚ) * ξ'.1 0` using `by rw [hl, hl', he1]`.

Conclude with `mul_left_cancel₀ (by exact_mod_cast hd.ne') this`. Take `⟨j, hj⟩` from `h3 ξ hξ ξ' hξ' h0`. Establish `hjR : (d : ℝ) * (((ξ.1 1 : ℚ) : ℝ) - ((ξ'.1 1 : ℚ) : ℝ)) = (j : ℝ)` using `by exact_mod_cast hj`. Establish `e : (d : ℝ) * (((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)) = (d : ℝ) * (((ξ'.1 0 : ℚ) : ℝ) * β + ((ξ'.1 1 : ℚ) : ℝ)) + (j : ℝ)`. Rewrite using `[← hjR, h0]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `he2` using `[e, round_add_intCast]`. Establish `hj0 : j = 0` using `by linarith`. Establish `h1' : ξ.1 1 = ξ'.1 1`. Rewrite `hj` using `[hj0]`.

Establish `: (d : ℚ) * (ξ.1 1 - ξ'.1 1) = 0` using `by simpa using hj`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `absurd h (by exact_mod_cast hd.ne')`. Conclude with `sub_eq_zero.mp h`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `h0`. Conclude with `h1'`. Establish `hb : ∀ ξ ∈ R, ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹ ≤ (C * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2)) * w (τ ξ)`.

Introduce `ξ hξ`. Establish `hν1 : 1 / ((d : ℝ) * Bu * T) ≤ |((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α`. Distinguish the cases in `hz : ξ.1 0 = 0`. Take `⟨l, hl⟩` from `h2 ξ hξ hz`. Establish `hlR : (d : ℝ) * ((ξ.1 1 : ℚ) : ℝ) = (l : ℝ)` using `by exact_mod_cast hl`.

Establish `hne : ξ.1 1 ≠ 0`. Introduce `h`. Apply `ξ.2` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `fin_cases i`.

Conclude with `hz`. Conclude with `h`. Establish `hl0 : l ≠ 0`. Introduce `h`. Rewrite `hl` using `[h]`.

Establish `: (d : ℚ) * ξ.1 1 = 0` using `by simpa using hl`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `absurd h (by exact_mod_cast hd.ne')`. Conclude with `hne h`. Establish `hl1 : (1 : ℝ) ≤ |(l : ℝ)|`.

Establish `: (1 : ℤ) ≤ |l|` using `Int.one_le_abs hl0`. Conclude with `this` after adjusting the coercions. Apply `lower_bound_second_case _ _ _ _ _ _ hd1 hBu hα hαT hT (abs_nonneg _) (abs_nonneg _)` to reduce the goal to its premises. Establish `hz' : ((ξ.1 0 : ℚ) : ℝ) = 0` using `by rw [hz]; simp`. Rewrite using `[hz', zero_mul, zero_add]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hlR, abs_mul, abs_of_pos hd0]`. Take `⟨l, hl⟩` from `h1 ξ hξ`. Establish `hlR : (d : ℝ) * ((ξ.1 0 : ℚ) : ℝ) = (l : ℝ)` using `by exact_mod_cast hl`. Establish `hl0 : l ≠ 0`.

Introduce `h`. Rewrite `hl` using `[h]`. Establish `: (d : ℚ) * ξ.1 0 = 0` using `by simpa using hl`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `absurd h (by exact_mod_cast hd.ne')`.

Conclude with `hz h`. Establish `hl1 : (1 : ℝ) ≤ |(l : ℝ)|`. Establish `: (1 : ℤ) ≤ |l|` using `Int.one_le_abs hl0`. Conclude with `this` after adjusting the coercions. Apply `lower_bound_first_case _ _ _ _ _ _ hd1 hBu hα hT (abs_nonneg _) (abs_nonneg _)` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hlR, abs_mul, abs_of_pos hd0]`. Establish `hL` using `round_bd ((d : ℝ) * ((ξ.1 0 : ℚ) : ℝ))`. Establish `hM` using `round_bd ((d : ℝ) * (((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)))`. Rewrite `hL`, `hM` using `[abs_mul, abs_of_pos hd0]`.

Conclude with `term_bd n κ Bu α T (d : ℝ) _ _ _ t _ _ hd1 hκ hκ1 hBu hα hαT hT (abs_nonneg _) (abs_nonneg _) ht rfl hν1 (abs_nonneg _) (abs_nonneg _) hL hM`. Establish `hf : ∀ ξ : {r : Fin 2 → ℚ // r ≠ 0}, 0 ≤ ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹`. Introduce `ξ`. Check the signs of the components of the expression. Take `⟨hs, hle⟩` from `gen R _ hf τ hinj w wsum hw0 (C * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2)) (by positivity) hb`.

Use `⟨hs, hle.trans (le_of_eq ?_)⟩` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.summable_tsum_inv_one_add_height_pow_le :
    ∀ (n d : ℕ) (κ Bu : ℝ), 0 < d → 0 < κ → κ ≤ 1 → 1 ≤ Bu → ∃ B : ℝ, 0 ≤ B ∧
        ∀ (R : Set {r : Fin 2 → ℚ // r ≠ 0}) (β α T t : ℝ), 0 ≤ t → Bu⁻¹ ≤ α → α ≤ T → 1 ≤ T →
          (∀ ξ ∈ R, ∃ l : ℤ, (d : ℚ) * ξ.1 0 = l) →
          (∀ ξ ∈ R, ξ.1 0 = 0 → ∃ l : ℤ, (d : ℚ) * ξ.1 1 = l) →
          (∀ ξ ∈ R, ∀ ξ' ∈ R, ξ.1 0 = ξ'.1 0 → ∃ l : ℤ, (d : ℚ) * (ξ.1 1 - ξ'.1 1) = l) →
          Summable (R.indicator fun ξ : {r : Fin 2 → ℚ // r ≠ 0} =>
            ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹) ∧
          ∑' ξ : {r : Fin 2 → ℚ // r ≠ 0}, R.indicator (fun ξ : {r : Fin 2 → ℚ // r ≠ 0} =>
            ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹) ξ
            ≤ B * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2) := by
  intro n d κ Bu hd hκ hκ1 hBu
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hBu0 : 0 < Bu := by linarith
  set w : ℤ × ℤ → ℝ := fun p => ((1 + |(p.1 : ℝ)|) ^ 2)⁻¹ * ((1 + |(p.2 : ℝ)|) ^ 2)⁻¹ with hw
  have hw0 : ∀ p, 0 ≤ w p := fun p => by simp only [hw]; positivity
  set C : ℝ := 16 * ((d : ℝ) * Bu / κ) ^ n * (((d : ℝ) / κ) * (Bu * (d : ℝ) / κ)) ^ 2 with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  refine ⟨C * ∑' p, w p, mul_nonneg hC0 (tsum_nonneg hw0), ?_⟩
  intro R β α T t ht hα hαT hT h1 h2 h3
  have hα0 : 0 < α := lt_of_lt_of_le (inv_pos.mpr hBu0) hα
  have hT0 : 0 < T := by linarith
  set τ : {r : Fin 2 → ℚ // r ≠ 0} → ℤ × ℤ := fun ξ =>
    (round ((d : ℝ) * ((ξ.1 0 : ℚ) : ℝ)),
      round ((d : ℝ) * (((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)))) with hτ
  have hinj : Set.InjOn τ R := by
    intro ξ hξ ξ' hξ' he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    simp only [hτ] at he1 he2
    obtain ⟨l, hl⟩ := h1 ξ hξ
    obtain ⟨l', hl'⟩ := h1 ξ' hξ'
    have hlR : (d : ℝ) * ((ξ.1 0 : ℚ) : ℝ) = (l : ℝ) := by exact_mod_cast hl
    have hlR' : (d : ℝ) * ((ξ'.1 0 : ℚ) : ℝ) = (l' : ℝ) := by exact_mod_cast hl'
    rw [hlR, hlR', round_intCast, round_intCast] at he1
    have h0 : ξ.1 0 = ξ'.1 0 := by
      have : (d : ℚ) * ξ.1 0 = (d : ℚ) * ξ'.1 0 := by rw [hl, hl', he1]
      exact mul_left_cancel₀ (by exact_mod_cast hd.ne') this
    obtain ⟨j, hj⟩ := h3 ξ hξ ξ' hξ' h0
    have hjR : (d : ℝ) * (((ξ.1 1 : ℚ) : ℝ) - ((ξ'.1 1 : ℚ) : ℝ)) = (j : ℝ) := by exact_mod_cast hj
    have e : (d : ℝ) * (((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ))
        = (d : ℝ) * (((ξ'.1 0 : ℚ) : ℝ) * β + ((ξ'.1 1 : ℚ) : ℝ)) + (j : ℝ) := by
      rw [← hjR, h0]; ring
    rw [e, round_add_intCast] at he2
    have hj0 : j = 0 := by linarith
    have h1' : ξ.1 1 = ξ'.1 1 := by
      rw [hj0] at hj
      have : (d : ℚ) * (ξ.1 1 - ξ'.1 1) = 0 := by simpa using hj
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (by exact_mod_cast hd.ne')
      · exact sub_eq_zero.mp h
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h0
    · exact h1'
  have hb : ∀ ξ ∈ R, ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹
      ≤ (C * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2)) * w (τ ξ) := by
    intro ξ hξ
    have hν1 : 1 / ((d : ℝ) * Bu * T) ≤ |((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α := by
      by_cases hz : ξ.1 0 = 0
      · obtain ⟨l, hl⟩ := h2 ξ hξ hz
        have hlR : (d : ℝ) * ((ξ.1 1 : ℚ) : ℝ) = (l : ℝ) := by exact_mod_cast hl
        have hne : ξ.1 1 ≠ 0 := by
          intro h
          apply ξ.2
          funext i
          fin_cases i
          · exact hz
          · exact h
        have hl0 : l ≠ 0 := by
          intro h
          rw [h] at hl
          have : (d : ℚ) * ξ.1 1 = 0 := by simpa using hl
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h (by exact_mod_cast hd.ne')
          · exact hne h
        have hl1 : (1 : ℝ) ≤ |(l : ℝ)| := by
          have : (1 : ℤ) ≤ |l| := Int.one_le_abs hl0
          exact_mod_cast this
        apply lower_bound_second_case _ _ _ _ _ _ hd1 hBu hα hαT hT (abs_nonneg _) (abs_nonneg _)
        have hz' : ((ξ.1 0 : ℚ) : ℝ) = 0 := by rw [hz]; simp
        rw [hz', zero_mul, zero_add]
        calc (1 : ℝ) ≤ |(l : ℝ)| := hl1
          _ = (d : ℝ) * |((ξ.1 1 : ℚ) : ℝ)| := by
            rw [← hlR, abs_mul, abs_of_pos hd0]
      · obtain ⟨l, hl⟩ := h1 ξ hξ
        have hlR : (d : ℝ) * ((ξ.1 0 : ℚ) : ℝ) = (l : ℝ) := by exact_mod_cast hl
        have hl0 : l ≠ 0 := by
          intro h
          rw [h] at hl
          have : (d : ℚ) * ξ.1 0 = 0 := by simpa using hl
          rcases mul_eq_zero.mp this with h | h
          · exact absurd h (by exact_mod_cast hd.ne')
          · exact hz h
        have hl1 : (1 : ℝ) ≤ |(l : ℝ)| := by
          have : (1 : ℤ) ≤ |l| := Int.one_le_abs hl0
          exact_mod_cast this
        apply lower_bound_first_case _ _ _ _ _ _ hd1 hBu hα hT (abs_nonneg _) (abs_nonneg _)
        calc (1 : ℝ) ≤ |(l : ℝ)| := hl1
          _ = (d : ℝ) * |((ξ.1 0 : ℚ) : ℝ)| := by
            rw [← hlR, abs_mul, abs_of_pos hd0]
    have hL := round_bd ((d : ℝ) * ((ξ.1 0 : ℚ) : ℝ))
    have hM := round_bd ((d : ℝ) * (((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)))
    rw [abs_mul, abs_of_pos hd0] at hL hM
    exact term_bd n κ Bu α T (d : ℝ) _ _ _ t _ _ hd1 hκ hκ1 hBu hα hαT hT (abs_nonneg _)
      (abs_nonneg _) ht rfl hν1 (abs_nonneg _) (abs_nonneg _) hL hM
  have hf : ∀ ξ : {r : Fin 2 → ℚ // r ≠ 0}, 0 ≤ ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹ := by
    intro ξ
    positivity
  obtain ⟨hs, hle⟩ := gen R _ hf τ hinj w wsum hw0 (C * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2))
    (by positivity) hb
  refine ⟨hs, hle.trans (le_of_eq ?_)⟩
  ring
