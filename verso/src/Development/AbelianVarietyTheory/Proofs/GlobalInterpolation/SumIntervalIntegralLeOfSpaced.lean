import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `hfc : Continuous f` using `continuous_iff_continuousAt.2 fun t => (hf t).continuousAt`. Establish `hF : ∀ t, HasDerivAt (fun t => (t - x - δ) / δ * f t) (f t / δ + (t - x - δ) / δ * f' t) t`. Introduce `t`. Establish `h1 : HasDerivAt (fun t : ℝ => (t - x - δ) / δ) (1 / δ) t` using `(((hasDerivAt_id t).sub_const x).sub_const δ).div_const δ`. Conclude with `(h1.fun_mul (hf t)).congr_deriv (by ring)`.

Establish `hc : Continuous fun t => f t / δ + (t - x - δ) / δ * f' t` using `by fun_prop`. Establish `h2` using `intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := x + δ) (fun t _ => hF t) (hc.intervalIntegrable _ _)`. Establish `h3 : (x + δ - x - δ) / δ * f (x + δ) - (x - x - δ) / δ * f x = f x`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h2` using `[h3]`. Rewrite using `[← h2]`. Apply `intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)` to reduce the goal to its premises. Introduce `t ht`. Establish `h4 : |(t - x - δ) / δ| ≤ 1`.

Rewrite using `[abs_div, abs_of_pos hδ, div_le_one hδ, abs_le]`. Apply the tactic sequence `constructor <;> linarith [ht.1, ht.2]`. Establish `h5 : (t - x - δ) / δ * f' t ≤ h t`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gallagher_interval (f f' h : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') (hh : Continuous h) (hb : ∀ t, |f' t| ≤ h t) (x δ : ℝ) (hδ : 0 < δ) :
    f x ≤ ∫ t in x..(x + δ), (f t / δ + h t) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have hF : ∀ t, HasDerivAt (fun t => (t - x - δ) / δ * f t) (f t / δ + (t - x - δ) / δ * f' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t - x - δ) / δ) (1 / δ) t :=
      (((hasDerivAt_id t).sub_const x).sub_const δ).div_const δ
    exact (h1.fun_mul (hf t)).congr_deriv (by ring)
  have hc : Continuous fun t => f t / δ + (t - x - δ) / δ * f' t := by fun_prop
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := x + δ)
    (fun t _ => hF t) (hc.intervalIntegrable _ _)
  have h3 : (x + δ - x - δ) / δ * f (x + δ) - (x - x - δ) / δ * f x = f x := by
    field_simp
    ring
  rw [h3] at h2
  rw [← h2]
  apply intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro t ht
  have h4 : |(t - x - δ) / δ| ≤ 1 := by
    rw [abs_div, abs_of_pos hδ, div_le_one hδ, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h5 : (t - x - δ) / δ * f' t ≤ h t := by
    calc _ ≤ |(t - x - δ) / δ * f' t| := le_abs_self _
      _ = |(t - x - δ) / δ| * |f' t| := abs_mul _ _
      _ ≤ 1 * h t := mul_le_mul h4 (hb t) (abs_nonneg _) zero_le_one
      _ = h t := one_mul _
  linarith

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Establish `hc : (2 * Real.pi * I * ((n : ℂ) - m)) ≠ 0`. Establish `: (n : ℂ) - m ≠ 0` using `sub_ne_zero.2 (by exact_mod_cast h)`.

Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Simplify using `[this, hpi, I_ne_zero]`. Rewrite using `[integral_exp_mul_complex hc]`. Establish `: Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * ((y + 1 : ℝ) : ℂ)) = Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * (y : ℂ))`. Establish `h1` using `Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)`.

Rewrite using `[show 2 * Real.pi * I * ((n : ℂ) - m) * ((y + 1 : ℝ) : ℂ) = 2 * Real.pi * I * ((n : ℂ) - m) * (y : ℂ) + (((n : ℤ) - m : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring, Complex.exp_add, h1, mul_one]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem integral_exp_two_pi_sub (n m : ℕ) (y : ℝ) :
    ∫ t in y..(y + 1), Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * t) = if n = m then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · have hc : (2 * Real.pi * I * ((n : ℂ) - m)) ≠ 0 := by
      have : (n : ℂ) - m ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this, hpi, I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * ((y + 1 : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * (y : ℂ)) := by
      have h1 := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
      rw [show 2 * Real.pi * I * ((n : ℂ) - m) * ((y + 1 : ℝ) : ℂ)
        = 2 * Real.pi * I * ((n : ℂ) - m) * (y : ℂ) + (((n : ℤ) - m : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, h1, mul_one]
    rw [this]; simp

/- English proof (translation)
Establish `: ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) = Complex.exp (((-(2 * Real.pi * c * t) : ℝ) : ℂ) * I) * ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm, ← Complex.exp_add]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]`.
-/
theorem norm_expSum_shift (s : Finset ℕ) (b : ℕ → ℂ) (c t : ℝ) :
    ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t)‖
      = ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ := by
  have : ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t)
      = Complex.exp (((-(2 * Real.pi * c * t) : ℝ) : ℂ) * I) *
        ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/- English proof (translation)
Establish `key : ∀ t : ℝ, ((‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ ^ 2 : ℝ) : ℂ) = ∑ n ∈ s, ∑ m ∈ s, b n * (starRingEnd ℂ) (b m) * Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * t)`. Introduce `t`. Rewrite using `[Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← Complex.exp_conj]`.

Simplify using `only [map_mul, conj_ofReal, conj_I, map_natCast, map_ofNat]`. Rewrite using `[mul_mul_mul_comm, ← Complex.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Apply `Complex.ofReal_injective` to reduce the goal to its premises.

Rewrite using `[← intervalIntegral.integral_ofReal]`. Repeatedly rewrite using `[key]`. Rewrite using `[intervalIntegral.integral_finset_sum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]`. Use `push_cast`. Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations.

Rewrite using `[intervalIntegral.integral_finset_sum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]`. Repeatedly rewrite using `[intervalIntegral.integral_const_mul, integral_exp_two_pi_sub]`. Simplify using `[hn, Complex.mul_conj']`.
-/
theorem integral_norm_sq_expSum (s : Finset ℕ) (b : ℕ → ℂ) (y : ℝ) :
    ∫ t in y..(y + 1), ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ ^ 2
      = ∑ n ∈ s, ‖b n‖ ^ 2 := by
  have key : ∀ t : ℝ, ((‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s, b n * (starRingEnd ℂ) (b m) *
        Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * t) := by
    intro t
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    simp only [map_mul, conj_ofReal, conj_I, map_natCast, map_ofNat]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [key]
  rw [intervalIntegral.integral_finset_sum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [intervalIntegral.integral_finset_sum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_sub]
  simp [hn, Complex.mul_conj']

/- English proof (translation)
Establish `hi : ∀ u v : ℝ, IntegrableOn g (Set.Ioc u v)` using `fun u v => (hg.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self`. Rewrite using `[intervalIntegral.integral_of_le (by linarith : y ≤ y + 1)]`. Rewrite using `[Finset.sum_congr rfl fun x _ => intervalIntegral.integral_of_le (by linarith : p x ≤ p x + δ)]`. Rewrite using `[← integral_biUnion_finset S (s := fun x => Set.Ioc (p x) (p x + δ)) (fun _ _ => measurableSet_Ioc) ?_ (fun x _ => hi _ _)]`. Apply `setIntegral_mono_set (hi _ _) (Filter.Eventually.of_forall h0)` to reduce the goal to its premises.

Apply `HasSubset.Subset.eventuallyLE` to reduce the goal to its premises. Introduce `t ht`. Simplify using `only [Set.mem_iUnion] at ht`. Take `⟨x, hx, ht⟩` from `ht`. Conclude with `⟨lt_of_le_of_lt (h1 x hx) ht.1, ht.2.trans (h2 x hx)⟩`.

Introduce `x hx z hz hxz`. Use `h3 x hx z hz hxz` as an intermediate fact. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `t ht ht'`. Establish `: |p x - p z| < δ`.

Apply the tactic sequence `rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_intervalIntegral_le_of_spaced (g : ℝ → ℝ) (hg : Continuous g) (h0 : ∀ t, 0 ≤ g t)
    (S : Finset ℝ) (p : ℝ → ℝ) (δ y : ℝ) (hδ : 0 < δ)
    (h1 : ∀ x ∈ S, y ≤ p x) (h2 : ∀ x ∈ S, p x + δ ≤ y + 1)
    (h3 : ∀ x ∈ S, ∀ z ∈ S, x ≠ z → δ ≤ |p x - p z|) :
    ∑ x ∈ S, ∫ t in (p x)..(p x + δ), g t ≤ ∫ t in y..(y + 1), g t := by
  have hi : ∀ u v : ℝ, IntegrableOn g (Set.Ioc u v) := fun u v =>
    (hg.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le (by linarith : y ≤ y + 1)]
  rw [Finset.sum_congr rfl fun x _ =>
    intervalIntegral.integral_of_le (by linarith : p x ≤ p x + δ)]
  rw [← integral_biUnion_finset S (s := fun x => Set.Ioc (p x) (p x + δ))
    (fun _ _ => measurableSet_Ioc) ?_ (fun x _ => hi _ _)]
  · apply setIntegral_mono_set (hi _ _) (Filter.Eventually.of_forall h0)
    apply HasSubset.Subset.eventuallyLE
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨x, hx, ht⟩ := ht
    exact ⟨lt_of_le_of_lt (h1 x hx) ht.1, ht.2.trans (h2 x hx)⟩
  · intro x hx z hz hxz
    have := h3 x hx z hz hxz
    rw [Function.onFun, Set.disjoint_left]
    intro t ht ht'
    have : |p x - p z| < δ := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
    linarith

/- English proof (translation)
Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Establish `h1` using `Complex.exp_int_mul_two_pi_mul_I (-(n * k))`. Rewrite using `[show 2 * Real.pi * I * (n : ℂ) * ((x - k : ℝ) : ℂ) = 2 * Real.pi * I * n * x + ((-(n * k) : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring, Complex.exp_add, h1, mul_one]`.
-/
theorem expSum_sub_int (s : Finset ℕ) (b : ℕ → ℂ) (x : ℝ) (k : ℤ) :
    ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * ((x - k : ℝ) : ℂ))
      = ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * x) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 := Complex.exp_int_mul_two_pi_mul_I (-(n * k))
  rw [show 2 * Real.pi * I * (n : ℂ) * ((x - k : ℝ) : ℂ)
    = 2 * Real.pi * I * n * x + ((-(n * k) : ℤ) : ℂ) * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_add, h1, mul_one]

/- English proof (translation)
Introduce `M N a S δ hδ hδ1 hS`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Simplify using the standard rewrite rules. Break down `S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩` into its components or cases. Simplify using `only [Finset.sum_empty]`.

Check the signs of the components of the expression. Use `set s := Finset.Ioc M (M + N) with hs`. Use `set c : ℝ := M + N / 2 with hc`. Use `set L : ℝ := Real.pi * N with hL`. Establish `hL0 : 0 < L` using `by positivity`.

Use `set b : ℕ → ℂ := fun n => a n * (2 * Real.pi * I * ((n : ℂ) - c)) with hb`. Use `set T : ℝ → ℂ := fun t => ∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) with hT`. Use `set T' : ℝ → ℂ := fun t => ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) with hT'`. Establish `hd : ∀ t, HasDerivAt T (T' t) t`. Introduce `t`.

Apply `HasDerivAt.fun_sum` to reduce the goal to its premises. Introduce `n _`. Establish `h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * I * ((n : ℂ) - c) * (t : ℂ)) (2 * Real.pi * I * ((n : ℂ) - c)) t`. Simplify using `using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (2 * Real.pi * I * ((n : ℂ) - c))`. Conclude with `((h1.cexp).const_mul (a n)).congr_deriv (by simp only [hb]; ring)`.

Establish `hTc : Continuous T` using `by simp only [hT]; fun_prop`. Establish `hTc' : Continuous T'` using `by simp only [hT']; fun_prop`. Establish `hG : ∀ x, ‖T x‖ ^ 2 ≤ ∫ t in x..(x + δ), (‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L))`. Introduce `x`. Use `gallagher_interval (fun t => ‖T t‖ ^ 2) (fun t => 2 * inner ℝ (T t) (T' t)) (fun t => L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L) (fun t => (hd t).norm_sq) (by fun_prop) (by fun_prop) ?_ x δ hδ` and prove the remaining obligations.

Introduce `t`. Establish `h1` using `abs_real_inner_le_norm (T t) (T' t)`. Rewrite using `[abs_mul, abs_two]`. Establish `h2 : L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L - 2 * (‖T t‖ * ‖T' t‖) = (L * ‖T t‖ - ‖T' t‖) ^ 2 / L` using `by field_simp; ring`. Establish `h3 : 0 ≤ (L * ‖T t‖ - ‖T' t‖) ^ 2 / L` using `by positivity`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set p : ℝ → ℝ := fun x => x - (⌊x - y⌋ : ℤ) with hp`. Establish `hsum` using `sum_intervalIntegral_le_of_spaced (fun t => ‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L)) (by fun_prop) (fun t => by positivity) S p δ y hδ (fun x _ => by simp only [hp]; linarith [Int.floor_le (x - y)]) ?_ ?_`. Establish `e1 : ∫ t in y..(y + 1), ‖T t‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2`. Simplify using `only [hT, norm_expSum_shift]`.

Conclude with `integral_norm_sq_expSum s a y`. Establish `e2 : ∫ t in y..(y + 1), ‖T' t‖ ^ 2 = ∑ n ∈ s, ‖b n‖ ^ 2`. Simplify using `only [hT', norm_expSum_shift]`. Conclude with `integral_norm_sq_expSum s b y`. Establish `e3 : ∑ n ∈ s, ‖b n‖ ^ 2 ≤ L ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2`.

Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun n hn => ?_` and prove the remaining obligations. Rewrite `hn` using `[hs, Finset.mem_Ioc]`. Establish `hn1 : (M : ℝ) < n` using `by exact_mod_cast hn.1`. Establish `hn2 : (n : ℝ) ≤ M + N` using `by exact_mod_cast hn.2`.

Establish `h4 : ‖(n : ℂ) - c‖ ≤ N / 2`. Rewrite using `[show (n : ℂ) - c = ((n - c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `h5 : ‖b n‖ ≤ L * ‖a n‖`. Simplify using `only [hb, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_ofNat]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_pow]`. Use `gcongr`. Establish `e4 : ∫ t in y..(y + 1), (‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L)) = (∑ n ∈ s, ‖a n‖ ^ 2) / δ + (L * ∑ n ∈ s, ‖a n‖ ^ 2 + (∑ n ∈ s, ‖b n‖ ^ 2) / L)`. Rewrite using `[intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral. …`.

Establish `e5 : (∑ n ∈ s, ‖b n‖ ^ 2) / L ≤ L * ∑ n ∈ s, ‖a n‖ ^ 2`. Rewrite using `[div_le_iff₀ hL0]`. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Simplify using `only [hT, hp]`. Rewrite using `[norm_expSum_shift, expSum_sub_int]`. Use `_ ≤ _ := Finset.sum_le_sum fun x _ => hG (p x)`. Use `_ ≤ _ := hsum`. Use `_ = _ := e4`.

Use `_ ≤ (∑ n ∈ s, ‖a n‖ ^ 2) / δ + (L * ∑ n ∈ s, ‖a n‖ ^ 2 + L * ∑ n ∈ s, ‖a n‖ ^ 2) := by`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = _ := by rw [hL]; ring`. Introduce `x hx`. Simplify using `only [hp]`.

Distinguish the cases in `hxy : x = y`. Substitute `hxy` using the available equality. Simplify using `[hδ1]`. Establish `h1` using `hS x hx y hy hxy (⌊x - y⌋ + 1)`. Establish `h2` using `Int.lt_floor_add_one (x - y)`.

Move the coercions through the operations in `at h1`. Rewrite `h1` using `[abs_of_neg (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `x hx z hz hxz`. Establish `h1` using `hS x hx z hz hxz (⌊x - y⌋ - ⌊z - y⌋)`.

Simplify using `only [hp]`. Use `h1 using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem additive_large_sieve : ∀ (M N : ℕ) (a : ℕ → ℂ) (S : Finset ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ k : ℤ, δ ≤ |x - y - k|) → ∑ x ∈ S, ‖∑ n ∈ Finset.Ioc M (M + N), a n * Complex.exp (2 * Real.pi * I * n * x)‖ ^ 2 ≤ (1 / δ + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  intro M N a S δ hδ hδ1 hS
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · simp only [Finset.sum_empty]; positivity
  set s := Finset.Ioc M (M + N) with hs
  set c : ℝ := M + N / 2 with hc
  set L : ℝ := Real.pi * N with hL
  have hL0 : 0 < L := by positivity
  set b : ℕ → ℂ := fun n => a n * (2 * Real.pi * I * ((n : ℂ) - c)) with hb
  set T : ℝ → ℂ := fun t => ∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) with hT
  set T' : ℝ → ℂ := fun t => ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) with hT'
  have hd : ∀ t, HasDerivAt T (T' t) t := by
    intro t
    apply HasDerivAt.fun_sum
    intro n _
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * I * ((n : ℂ) - c) * (t : ℂ))
        (2 * Real.pi * I * ((n : ℂ) - c)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (2 * Real.pi * I * ((n : ℂ) - c))
    exact ((h1.cexp).const_mul (a n)).congr_deriv (by simp only [hb]; ring)
  have hTc : Continuous T := by simp only [hT]; fun_prop
  have hTc' : Continuous T' := by simp only [hT']; fun_prop
  have hG : ∀ x, ‖T x‖ ^ 2 ≤ ∫ t in x..(x + δ), (‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L)) := by
    intro x
    refine gallagher_interval (fun t => ‖T t‖ ^ 2) (fun t => 2 * inner ℝ (T t) (T' t))
      (fun t => L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L) (fun t => (hd t).norm_sq) (by fun_prop) (by fun_prop) ?_ x δ hδ
    intro t
    have h1 := abs_real_inner_le_norm (T t) (T' t)
    rw [abs_mul, abs_two]
    have h2 : L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L - 2 * (‖T t‖ * ‖T' t‖)
        = (L * ‖T t‖ - ‖T' t‖) ^ 2 / L := by field_simp; ring
    have h3 : 0 ≤ (L * ‖T t‖ - ‖T' t‖) ^ 2 / L := by positivity
    linarith
  set p : ℝ → ℝ := fun x => x - (⌊x - y⌋ : ℤ) with hp
  have hsum := sum_intervalIntegral_le_of_spaced
    (fun t => ‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L)) (by fun_prop) (fun t => by positivity)
    S p δ y hδ (fun x _ => by simp only [hp]; linarith [Int.floor_le (x - y)]) ?_ ?_
  · have e1 : ∫ t in y..(y + 1), ‖T t‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
      simp only [hT, norm_expSum_shift]; exact integral_norm_sq_expSum s a y
    have e2 : ∫ t in y..(y + 1), ‖T' t‖ ^ 2 = ∑ n ∈ s, ‖b n‖ ^ 2 := by
      simp only [hT', norm_expSum_shift]; exact integral_norm_sq_expSum s b y
    have e3 : ∑ n ∈ s, ‖b n‖ ^ 2 ≤ L ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      rw [hs, Finset.mem_Ioc] at hn
      have hn1 : (M : ℝ) < n := by exact_mod_cast hn.1
      have hn2 : (n : ℝ) ≤ M + N := by exact_mod_cast hn.2
      have h4 : ‖(n : ℂ) - c‖ ≤ N / 2 := by
        rw [show (n : ℂ) - c = ((n - c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      have h5 : ‖b n‖ ≤ L * ‖a n‖ := by
        simp only [hb, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos, Complex.norm_ofNat]
        calc ‖a n‖ * (2 * Real.pi * 1 * ‖(n : ℂ) - c‖) ≤ ‖a n‖ * (2 * Real.pi * 1 * (N / 2)) := by
              gcongr
          _ = L * ‖a n‖ := by rw [hL]; ring
      rw [← mul_pow]
      gcongr
    have e4 : ∫ t in y..(y + 1), (‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L))
        = (∑ n ∈ s, ‖a n‖ ^ 2) / δ + (L * ∑ n ∈ s, ‖a n‖ ^ 2 + (∑ n ∈ s, ‖b n‖ ^ 2) / L) := by
      rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_div,
        intervalIntegral.integral_div, intervalIntegral.integral_const_mul, e1, e2]
    have e5 : (∑ n ∈ s, ‖b n‖ ^ 2) / L ≤ L * ∑ n ∈ s, ‖a n‖ ^ 2 := by
      rw [div_le_iff₀ hL0]; nlinarith
    calc _ = ∑ x ∈ S, ‖T (p x)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [hT, hp]
          rw [norm_expSum_shift, expSum_sub_int]
      _ ≤ _ := Finset.sum_le_sum fun x _ => hG (p x)
      _ ≤ _ := hsum
      _ = _ := e4
      _ ≤ (∑ n ∈ s, ‖a n‖ ^ 2) / δ + (L * ∑ n ∈ s, ‖a n‖ ^ 2 + L * ∑ n ∈ s, ‖a n‖ ^ 2) := by
          linarith
      _ = _ := by rw [hL]; ring
  · intro x hx
    simp only [hp]
    by_cases hxy : x = y
    · subst hxy; simp [hδ1]
    · have h1 := hS x hx y hy hxy (⌊x - y⌋ + 1)
      have h2 := Int.lt_floor_add_one (x - y)
      push_cast at h1
      rw [abs_of_neg (by linarith)] at h1
      linarith
  · intro x hx z hz hxz
    have h1 := hS x hx z hz hxz (⌊x - y⌋ - ⌊z - y⌋)
    simp only [hp]
    convert h1 using 2
    push_cast; ring

end GlobalTheory
