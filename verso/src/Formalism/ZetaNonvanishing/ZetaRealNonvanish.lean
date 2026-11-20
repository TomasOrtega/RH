import Formalism.ZetaRealNonvanish

open Complex Set Filter Topology

noncomputable section

namespace Formalism

namespace ZRN

def e (n : ℕ) (s : ℂ) : ℂ :=
  (1 - s) * ((n : ℂ) + 1) ^ (-s) + ((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s)

def F (s : ℂ) : ℂ := ∑' n, e n s

/- English proof (translation)
Use `set x : ℝ := (n : ℝ) + 1 with hxdef`. Establish `hx0 : 0 < x` using `by positivity`. Use `set ℓ := Real.log x with hℓ`. Use `set ℓ' := Real.log (x + 1) with hℓ'`. Use `set L := ℓ' - ℓ with hL`.

Use `set a : ℂ := 1 - s with ha`. Establish `c1 : ∀ w : ℂ, ((n : ℂ) + 1) ^ w = exp ((ℓ : ℂ) * w)`. Introduce `w`. Establish `h1 : ((n : ℂ) + 1) = ((x : ℝ) : ℂ)` using `by rw [hxdef]; push_cast; ring`. Rewrite using `[h1, cpow_def_of_ne_zero (by exact_mod_cast hx0.ne'), ← Complex.ofReal_log hx0.le]`.

Establish `c2 : ∀ w : ℂ, ((n : ℂ) + 2) ^ w = exp ((ℓ' : ℂ) * w)`. Introduce `w`. Establish `h1 : ((n : ℂ) + 2) = ((x + 1 : ℝ) : ℂ)` using `by rw [hxdef]; push_cast; ring`. Rewrite using `[h1, cpow_def_of_ne_zero (by exact_mod_cast (by linarith : (0:ℝ) < x + 1).ne'), ← Complex.ofReal_log (by linarith)]`. Establish `hE1 : exp ((ℓ : ℂ) * -s) = exp ((ℓ : ℂ) * a) * ((x : ℂ))⁻¹`.

Establish `: (ℓ : ℂ) * -s = (ℓ : ℂ) * a + -(ℓ : ℂ)` using `by rw [ha]; ring`. Rewrite using `[this, Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp, hℓ, Real.exp_log hx0]`. Establish `hE2 : exp ((ℓ' : ℂ) * a) = exp ((ℓ : ℂ) * a) * exp (a * (L : ℂ))`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`.

Rewrite using `[hL]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `key : e n s = exp ((ℓ : ℂ) * a) * (-(exp (a * (L : ℂ)) - 1 - a * (L : ℂ)) + a * (((x : ℂ))⁻¹ - (L : ℂ)))`. Unfold `e`.

Rewrite using `[← ha, c1, c1, c2, hE1, hE2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hLle : L ≤ x⁻¹`. Use `Real.log_le_sub_one_of_pos (x := (x + 1) / x) (by positivity)` as an intermediate fact. Rewrite `this` using `[Real.log_div (by linarith) hx0.ne']`.

Rewrite using `[hL, hℓ, hℓ']`. Combine the equalities or inequalities in the displayed calculation. Establish `hLge : (x + 1)⁻¹ ≤ L`. Use `Real.one_sub_inv_le_log_of_pos (x := (x + 1) / x) (by positivity)` as an intermediate fact. Rewrite `this` using `[Real.log_div (by linarith) hx0.ne']`.

Rewrite using `[hL, hℓ, hℓ']`. Combine the equalities or inequalities in the displayed calculation. Establish `hL0 : 0 ≤ L` using `le_trans (by positivity) hLge`. Establish `hd : x⁻¹ - L ≤ (x ^ 2)⁻¹`. Establish `h3 : x⁻¹ - (x + 1)⁻¹ = (x * (x + 1))⁻¹` using `by field_simp; ring`.

Establish `h4 : (x * (x + 1))⁻¹ ≤ (x ^ 2)⁻¹` using `inv_anti₀ (by positivity) (by nlinarith)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hna : 0 ≤ ‖a‖` using `norm_nonneg _`. Establish `hnX : ‖exp ((ℓ : ℂ) * a)‖ = Real.exp (ℓ * (1 - s.re))`. Rewrite using `[Complex.norm_exp]`.

Use `congr 1`. Rewrite using `[ha]`. Simplify using the standard rewrite rules. Establish `hnaL : ‖a * (L : ℂ)‖ = ‖a‖ * L`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]`.

Establish `hz : ‖a * (L : ℂ)‖ ≤ 1`. Rewrite using `[hnaL]`. Combine the equalities or inequalities in the displayed calculation. Establish `hexp` using `Complex.norm_exp_sub_one_sub_id_le hz`. Establish `hsq : ‖a * (L : ℂ)‖ ^ 2 ≤ ‖a‖ ^ 2 * (x ^ 2)⁻¹`.

Rewrite using `[hnaL, mul_pow, ← inv_pow]`. Use `gcongr`. Establish `hlin : ‖a * (((x : ℂ))⁻¹ - (L : ℂ))‖ ≤ ‖a‖ * (x ^ 2)⁻¹`. Establish `: ((x : ℂ))⁻¹ - (L : ℂ) = ((x⁻¹ - L : ℝ) : ℂ)` using `by push_cast; ring`. Rewrite using `[this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]`.

Conclude with `mul_le_mul_of_nonneg_left hd hna`. Establish `hx2 : x ^ 2 = Real.exp (2 * ℓ)`. Rewrite using `[show 2 * ℓ = ℓ + ℓ by ring, Real.exp_add, hℓ, Real.exp_log hx0]; ring`. Rewrite using `[key, norm_mul, hnX]`. Combine the equalities or inequalities in the displayed calculation.

Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_neg]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = (‖a‖ ^ 2 + ‖a‖) * (Real.exp (ℓ * (1 - s.re)) * (x ^ 2)⁻¹) := by ring`. Use `_ = (‖a‖ ^ 2 + ‖a‖) * x ^ (-1 - s.re) := by`.

Use `congr 1`. Rewrite using `[Real.rpow_def_of_pos hx0, hx2, ← Real.exp_neg, ← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma e_bound (n : ℕ) (s : ℂ) (hs : ‖1 - s‖ ≤ (n : ℝ) + 1) :
    ‖e n s‖ ≤ (‖1 - s‖ ^ 2 + ‖1 - s‖) * ((n : ℝ) + 1) ^ (-1 - s.re) := by
  set x : ℝ := (n : ℝ) + 1 with hxdef
  have hx0 : 0 < x := by positivity
  set ℓ := Real.log x with hℓ
  set ℓ' := Real.log (x + 1) with hℓ'
  set L := ℓ' - ℓ with hL
  set a : ℂ := 1 - s with ha
  have c1 : ∀ w : ℂ, ((n : ℂ) + 1) ^ w = exp ((ℓ : ℂ) * w) := by
    intro w
    have h1 : ((n : ℂ) + 1) = ((x : ℝ) : ℂ) := by rw [hxdef]; push_cast; ring
    rw [h1, cpow_def_of_ne_zero (by exact_mod_cast hx0.ne'), ← Complex.ofReal_log hx0.le]
  have c2 : ∀ w : ℂ, ((n : ℂ) + 2) ^ w = exp ((ℓ' : ℂ) * w) := by
    intro w
    have h1 : ((n : ℂ) + 2) = ((x + 1 : ℝ) : ℂ) := by rw [hxdef]; push_cast; ring
    rw [h1, cpow_def_of_ne_zero (by exact_mod_cast (by linarith : (0:ℝ) < x + 1).ne'),
      ← Complex.ofReal_log (by linarith)]
  have hE1 : exp ((ℓ : ℂ) * -s) = exp ((ℓ : ℂ) * a) * ((x : ℂ))⁻¹ := by
    have : (ℓ : ℂ) * -s = (ℓ : ℂ) * a + -(ℓ : ℂ) := by rw [ha]; ring
    rw [this, Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp, hℓ, Real.exp_log hx0]
  have hE2 : exp ((ℓ' : ℂ) * a) = exp ((ℓ : ℂ) * a) * exp (a * (L : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; rw [hL]; push_cast; ring
  have key : e n s = exp ((ℓ : ℂ) * a) *
      (-(exp (a * (L : ℂ)) - 1 - a * (L : ℂ)) + a * (((x : ℂ))⁻¹ - (L : ℂ))) := by
    unfold e
    rw [← ha, c1, c1, c2, hE1, hE2]
    ring
  have hLle : L ≤ x⁻¹ := by
    have := Real.log_le_sub_one_of_pos (x := (x + 1) / x) (by positivity)
    rw [Real.log_div (by linarith) hx0.ne'] at this
    rw [hL, hℓ, hℓ']
    calc _ ≤ (x + 1) / x - 1 := this
      _ = x⁻¹ := by field_simp; ring
  have hLge : (x + 1)⁻¹ ≤ L := by
    have := Real.one_sub_inv_le_log_of_pos (x := (x + 1) / x) (by positivity)
    rw [Real.log_div (by linarith) hx0.ne'] at this
    rw [hL, hℓ, hℓ']
    calc (x + 1)⁻¹ = 1 - ((x + 1) / x)⁻¹ := by field_simp; ring
      _ ≤ _ := this
  have hL0 : 0 ≤ L := le_trans (by positivity) hLge
  have hd : x⁻¹ - L ≤ (x ^ 2)⁻¹ := by
    have h3 : x⁻¹ - (x + 1)⁻¹ = (x * (x + 1))⁻¹ := by field_simp; ring
    have h4 : (x * (x + 1))⁻¹ ≤ (x ^ 2)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
    linarith
  have hna : 0 ≤ ‖a‖ := norm_nonneg _
  have hnX : ‖exp ((ℓ : ℂ) * a)‖ = Real.exp (ℓ * (1 - s.re)) := by
    rw [Complex.norm_exp]; congr 1; rw [ha]; simp
  have hnaL : ‖a * (L : ℂ)‖ = ‖a‖ * L := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
  have hz : ‖a * (L : ℂ)‖ ≤ 1 := by
    rw [hnaL]
    calc ‖a‖ * L ≤ x * x⁻¹ := mul_le_mul hs hLle hL0 hx0.le
      _ = 1 := mul_inv_cancel₀ hx0.ne'
  have hexp := Complex.norm_exp_sub_one_sub_id_le hz
  have hsq : ‖a * (L : ℂ)‖ ^ 2 ≤ ‖a‖ ^ 2 * (x ^ 2)⁻¹ := by
    rw [hnaL, mul_pow, ← inv_pow]
    gcongr
  have hlin : ‖a * (((x : ℂ))⁻¹ - (L : ℂ))‖ ≤ ‖a‖ * (x ^ 2)⁻¹ := by
    have : ((x : ℂ))⁻¹ - (L : ℂ) = ((x⁻¹ - L : ℝ) : ℂ) := by push_cast; ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact mul_le_mul_of_nonneg_left hd hna
  have hx2 : x ^ 2 = Real.exp (2 * ℓ) := by
    rw [show 2 * ℓ = ℓ + ℓ by ring, Real.exp_add, hℓ, Real.exp_log hx0]; ring
  rw [key, norm_mul, hnX]
  calc Real.exp (ℓ * (1 - s.re)) *
        ‖-(exp (a * (L : ℂ)) - 1 - a * (L : ℂ)) + a * (((x : ℂ))⁻¹ - (L : ℂ))‖
      ≤ Real.exp (ℓ * (1 - s.re)) * (‖a‖ ^ 2 * (x ^ 2)⁻¹ + ‖a‖ * (x ^ 2)⁻¹) := by
        gcongr
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
        linarith
    _ = (‖a‖ ^ 2 + ‖a‖) * (Real.exp (ℓ * (1 - s.re)) * (x ^ 2)⁻¹) := by ring
    _ = (‖a‖ ^ 2 + ‖a‖) * x ^ (-1 - s.re) := by
        congr 1
        rw [Real.rpow_def_of_pos hx0, hx2, ← Real.exp_neg, ← Real.exp_add]
        congr 1
        ring

/- English proof (translation)
Use `norm_cpow_eq_rpow_re_of_pos hk w` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `this`.
-/
lemma norm_cpow_nat (n : ℕ) (k : ℝ) (hk : 0 < (n : ℝ) + k) (w : ℂ) :
    ‖((n : ℂ) + (k : ℂ)) ^ w‖ = ((n : ℝ) + k) ^ w.re := by
  have := norm_cpow_eq_rpow_re_of_pos hk w
  push_cast at this; exact this

/- English proof (translation)
Establish `h1` using `norm_cpow_nat n 1 (by positivity) (-s)`. Establish `h2` using `norm_cpow_nat n 1 (by positivity) (1 - s)`. Establish `h3` using `norm_cpow_nat n 2 (by positivity) (1 - s)`. Move the coercions through the operations in `at h1 h2 h3`. Establish `hx : (1 : ℝ) ≤ (n : ℝ) + 1` using `by have := n.cast_nonneg (α := ℝ); linarith`.

Establish `b1 : ((n : ℝ) + 1) ^ (-s).re ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx (by simp; linarith)`. Establish `b2 : ((n : ℝ) + 1) ^ (1 - s).re ≤ (n : ℝ) + 1`. Combine the equalities or inequalities in the displayed calculation. Establish `b3 : ((n : ℝ) + 2) ^ (1 - s).re ≤ (n : ℝ) + 2`. Combine the equalities or inequalities in the displayed calculation.

Unfold `e`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Use `gcongr`. Conclude with `norm_add_le _ _`.

Use `_ ≤ ‖1 - s‖ * 1 + ((n : ℝ) + 1) + ((n : ℝ) + 2) := by`. Rewrite using `[norm_mul, h1, h2, h3]`. Use `gcongr`. Use `_ = ‖1 - s‖ + 2 * ((n : ℝ) + 1) + 1 := by ring`.
-/
lemma e_crude (n : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ‖e n s‖ ≤ ‖1 - s‖ + 2 * ((n : ℝ) + 1) + 1 := by
  have h1 := norm_cpow_nat n 1 (by positivity) (-s)
  have h2 := norm_cpow_nat n 1 (by positivity) (1 - s)
  have h3 := norm_cpow_nat n 2 (by positivity) (1 - s)
  push_cast at h1 h2 h3
  have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
  have b1 : ((n : ℝ) + 1) ^ (-s).re ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by simp; linarith)
  have b2 : ((n : ℝ) + 1) ^ (1 - s).re ≤ (n : ℝ) + 1 := by
    calc ((n : ℝ) + 1) ^ (1 - s).re ≤ ((n : ℝ) + 1) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx (by simp; linarith)
      _ = (n : ℝ) + 1 := Real.rpow_one _
  have b3 : ((n : ℝ) + 2) ^ (1 - s).re ≤ (n : ℝ) + 2 := by
    calc ((n : ℝ) + 2) ^ (1 - s).re ≤ ((n : ℝ) + 2) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by simp; linarith)
      _ = (n : ℝ) + 2 := Real.rpow_one _
  unfold e
  calc ‖(1 - s) * ((n : ℂ) + 1) ^ (-s) + ((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s)‖
      ≤ ‖(1 - s) * ((n : ℂ) + 1) ^ (-s)‖ + ‖((n : ℂ) + 1) ^ (1 - s)‖
          + ‖((n : ℂ) + 2) ^ (1 - s)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ ‖1 - s‖ * 1 + ((n : ℝ) + 1) + ((n : ℝ) + 2) := by
        rw [norm_mul, h1, h2, h3]
        gcongr
    _ = ‖1 - s‖ + 2 * ((n : ℝ) + 1) + 1 := by ring

/- English proof (translation)
Establish `h1 : (n : ℂ) + 1 ≠ 0` using `by exact_mod_cast Nat.succ_ne_zero n`. Establish `h2 : (n : ℂ) + 2 ≠ 0` using `by exact_mod_cast (by omega : n + 2 ≠ 0)`. Introduce `s`. Unfold `e`. Use `fun_prop (disch := simp [h1, h2])`.
-/
lemma e_differentiable (n : ℕ) : Differentiable ℂ (e n) := by
  have h1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  intro s
  unfold e
  fun_prop (disch := simp [h1, h2])

/- English proof (translation)
Use `set δ := s₀.re / 2 with hδ`. Use `set R := ‖1 - s₀‖ + 1 with hR`. Establish `hδ0 : 0 < δ` using `by positivity`. Establish `hR0 : 0 ≤ R` using `by positivity`. Use `⟨min δ 1, lt_min hδ0 one_pos, fun n => (R ^ 2 + R) * ((n : ℝ) + 1) ^ (-1 - δ) + (if (n : ℝ) + 1 < R then R + 2 * ((n : ℝ) + 1) + 1 else 0), ?_, ?_⟩` and prove the remaining obligations.

Use `Summable.add ?_ ?_` and prove the remaining obligations. Use `Summable.mul_left _ ?_` and prove the remaining obligations. Use `(summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -1 - δ < -1))` as an intermediate fact. Use `this.congr (fun n => ?_)` and prove the remaining obligations. Use `push_cast`.

Put the polynomial expressions in normal form. Use `summable_of_ne_finset_zero (s := Finset.range ⌈R⌉₊) (fun n hn => ?_)` and prove the remaining obligations. Rewrite `hn` using `[Finset.mem_range, not_lt]`. Establish `: R ≤ (n : ℝ)` using `(Nat.le_ceil R).trans (by exact_mod_cast hn)`. Rewrite using `[if_neg (by linarith)]`.

Introduce `n w hw`. Rewrite `hw` using `[Metric.mem_ball, dist_eq_norm]`. Establish `hwr : ‖w - s₀‖ < δ` using `lt_of_lt_of_le hw (min_le_left _ _)`. Establish `hw1 : ‖w - s₀‖ < 1` using `lt_of_lt_of_le hw (min_le_right _ _)`. Establish `hre : δ < w.re`.

Use `Complex.abs_re_le_norm (w - s₀)` as an intermediate fact. Rewrite `this` using `[Complex.sub_re]`. Use `(abs_le.mp this).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hnorm : ‖1 - w‖ ≤ R`.

Combine the equalities or inequalities in the displayed calculation. Establish `hx : (1 : ℝ) ≤ (n : ℝ) + 1` using `by have := n.cast_nonneg (α := ℝ); linarith`. Establish `hfirst : 0 ≤ (R ^ 2 + R) * ((n : ℝ) + 1) ^ (-1 - δ)` using `by positivity`. Use `show ‖e n w‖ ≤ (R ^ 2 + R) * ((n : ℝ) + 1) ^ (-1 - δ) + (if (n : ℝ) + 1 < R then R + 2 * ((n : ℝ) + 1) + 1 else 0)`. Distinguish the cases in `hc : (n : ℝ) + 1 < R`.

Rewrite using `[if_pos hc]`. Use `e_crude n w (by linarith)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg hc, add_zero] replace hc := not_lt.mp hc`. Use `(e_bound n w (hnorm.trans hc)).trans ?_` and prove the remaining obligations.

Establish `hp : ((n : ℝ) + 1) ^ (-1 - w.re) ≤ ((n : ℝ) + 1) ^ (-1 - δ)` using `Real.rpow_le_rpow_of_exponent_le hx (by linarith)`. Establish `hq : ‖1 - w‖ ^ 2 + ‖1 - w‖ ≤ R ^ 2 + R`. Use `norm_nonneg (1 - w)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Conclude with `mul_le_mul hq hp (by positivity) (by positivity)`.
-/
lemma e_dom (s₀ : ℂ) (h : 0 < s₀.re) : ∃ r > 0, ∃ u : ℕ → ℝ, Summable u ∧
    ∀ n : ℕ, ∀ w ∈ Metric.ball s₀ r, ‖e n w‖ ≤ u n := by
  set δ := s₀.re / 2 with hδ
  set R := ‖1 - s₀‖ + 1 with hR
  have hδ0 : 0 < δ := by positivity
  have hR0 : 0 ≤ R := by positivity
  refine ⟨min δ 1, lt_min hδ0 one_pos,
    fun n => (R ^ 2 + R) * ((n : ℝ) + 1) ^ (-1 - δ) +
      (if (n : ℝ) + 1 < R then R + 2 * ((n : ℝ) + 1) + 1 else 0), ?_, ?_⟩
  · refine Summable.add ?_ ?_
    · refine Summable.mul_left _ ?_
      have := (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith : -1 - δ < -1))
      refine this.congr (fun n => ?_)
      push_cast; ring_nf
    · refine summable_of_ne_finset_zero (s := Finset.range ⌈R⌉₊) (fun n hn => ?_)
      rw [Finset.mem_range, not_lt] at hn
      have : R ≤ (n : ℝ) := (Nat.le_ceil R).trans (by exact_mod_cast hn)
      rw [if_neg (by linarith)]
  · intro n w hw
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have hwr : ‖w - s₀‖ < δ := lt_of_lt_of_le hw (min_le_left _ _)
    have hw1 : ‖w - s₀‖ < 1 := lt_of_lt_of_le hw (min_le_right _ _)
    have hre : δ < w.re := by
      have := Complex.abs_re_le_norm (w - s₀)
      rw [Complex.sub_re] at this
      have := (abs_le.mp this).1
      linarith
    have hnorm : ‖1 - w‖ ≤ R := by
      calc ‖1 - w‖ = ‖(1 - s₀) - (w - s₀)‖ := by ring_nf
        _ ≤ ‖1 - s₀‖ + ‖w - s₀‖ := norm_sub_le _ _
        _ ≤ R := by linarith
    have hx : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := n.cast_nonneg (α := ℝ); linarith
    have hfirst : 0 ≤ (R ^ 2 + R) * ((n : ℝ) + 1) ^ (-1 - δ) := by positivity
    show ‖e n w‖ ≤ (R ^ 2 + R) * ((n : ℝ) + 1) ^ (-1 - δ) +
      (if (n : ℝ) + 1 < R then R + 2 * ((n : ℝ) + 1) + 1 else 0)
    by_cases hc : (n : ℝ) + 1 < R
    · rw [if_pos hc]
      have := e_crude n w (by linarith)
      linarith
    · rw [if_neg hc, add_zero]
      replace hc := not_lt.mp hc
      refine (e_bound n w (hnorm.trans hc)).trans ?_
      have hp : ((n : ℝ) + 1) ^ (-1 - w.re) ≤ ((n : ℝ) + 1) ^ (-1 - δ) :=
        Real.rpow_le_rpow_of_exponent_le hx (by linarith)
      have hq : ‖1 - w‖ ^ 2 + ‖1 - w‖ ≤ R ^ 2 + R := by
        have := norm_nonneg (1 - w)
        nlinarith
      exact mul_le_mul hq hp (by positivity) (by positivity)

/- English proof (translation)
Take `⟨r, hr, u, hu, hb⟩` from `e_dom s₀ h`. Establish `hd : DifferentiableOn ℂ F (Metric.ball s₀ r)` using `differentiableOn_tsum_of_summable_norm hu (fun n => (e_differentiable n).differentiableOn) Metric.isOpen_ball hb`. Conclude with `hd.differentiableAt (Metric.ball_mem_nhds s₀ hr)`.
-/
lemma F_differentiableAt (s₀ : ℂ) (h : 0 < s₀.re) : DifferentiableAt ℂ F s₀ := by
  obtain ⟨r, hr, u, hu, hb⟩ := e_dom s₀ h
  have hd : DifferentiableOn ℂ F (Metric.ball s₀ r) :=
    differentiableOn_tsum_of_summable_norm hu (fun n => (e_differentiable n).differentiableOn)
      Metric.isOpen_ball hb
  exact hd.differentiableAt (Metric.ball_mem_nhds s₀ hr)

/- English proof (translation)
Take `⟨r, hr, u, hu, hb⟩` from `e_dom s h`. Conclude with `Summable.of_norm_bounded hu (fun n => hb n s (Metric.mem_ball_self hr))`.
-/
lemma summable_e (s : ℂ) (h : 0 < s.re) : Summable (fun n => e n s) := by
  obtain ⟨r, hr, u, hu, hb⟩ := e_dom s h
  exact Summable.of_norm_bounded hu (fun n => hb n s (Metric.mem_ball_self hr))

/- English proof (translation)
Establish `hS` using `summable_e s (by linarith)`. Establish `hz : riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s` using `zeta_eq_tsum_one_div_nat_add_one_cpow h`. Establish `hA : Summable (fun n : ℕ => (1 - s) * ((n : ℂ) + 1) ^ (-s))`. Use `(summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr h)` as an intermediate fact. Use `(this.mul_left (1 - s)).congr (fun n => ?_)` and prove the remaining obligations.

Use `push_cast`. Rewrite using `[cpow_neg, one_div]`. Establish `hB : Summable (fun n : ℕ => ((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s))`. Use `(hS.sub hA).congr (fun n => ?_)` and prove the remaining obligations. Simplify using `only [e]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hp : ∀ N : ℕ, ∑ n ∈ Finset.range N, (((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s)) = 1 - ((N : ℂ) + 1) ^ (1 - s)`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => simp`.

Consider the case `succ N ih => rw [Finset.sum_range_succ, ih]`. Use `push_cast`. Put the polynomial expressions in normal form. Establish `hlim0 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0)`. Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`.

Establish `e1 : ∀ N : ℕ, ‖((N : ℂ) + 1) ^ (1 - s)‖ = ((N : ℝ) + 1) ^ (1 - s.re)`. Introduce `N`. Use `norm_cpow_nat N 1 (by positivity) (1 - s)` as an intermediate fact. Move the coercions through the operations in `at this`. Simplify using `using this`.

Repeatedly rewrite using `[e1]`. Establish `hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop` using `tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop`. Use `(tendsto_rpow_neg_atTop (y := s.re - 1) (by linarith)).comp hN` as an intermediate fact. Use `this.congr (fun N => ?_)` and prove the remaining obligations. Simplify using `only [Function.comp_apply, neg_sub]`.

Establish `htB : ∑' n : ℕ, (((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s)) = 1`. Establish `ht` using `hB.hasSum.tendsto_sum_nat`. Rewrite `ht` using `[hp]`. Establish `hlim : Tendsto (fun N : ℕ => 1 - ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 1)`. Simplify using `using tendsto_const_nhds.sub hlim0`.

Conclude with `tendsto_nhds_unique ht hlim`. Unfold `F`. Combine the equalities or inequalities in the displayed calculation. Use `tsum_congr (fun n => ?_)` and prove the remaining obligations. Simplify using `only [e]`.

Expand and normalize the polynomial expressions, which then agree. Use `_ = (1 - s) * riemannZeta s + 1 := by`. Rewrite using `[hA.tsum_add hB, htB, tsum_mul_left, hz]`. Use `congr 2`. Use `tsum_congr (fun n => ?_)` and prove the remaining obligations.

Rewrite using `[cpow_neg, one_div]`. Use `_ = 1 + (1 - s) * riemannZeta s := by ring`.
-/
lemma F_eq (s : ℂ) (h : 1 < s.re) : F s = 1 + (1 - s) * riemannZeta s := by
  have hS := summable_e s (by linarith)
  have hz : riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s := zeta_eq_tsum_one_div_nat_add_one_cpow h
  have hA : Summable (fun n : ℕ => (1 - s) * ((n : ℂ) + 1) ^ (-s)) := by
    have := (summable_nat_add_iff 1).mpr (Complex.summable_one_div_nat_cpow.mpr h)
    refine (this.mul_left (1 - s)).congr (fun n => ?_)
    push_cast; rw [cpow_neg, one_div]
  have hB : Summable (fun n : ℕ => ((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s)) := by
    refine (hS.sub hA).congr (fun n => ?_); simp only [e]; ring
  have hp : ∀ N : ℕ, ∑ n ∈ Finset.range N, (((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s))
      = 1 - ((N : ℂ) + 1) ^ (1 - s) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_range_succ, ih]; push_cast; ring_nf
  have hlim0 : Tendsto (fun N : ℕ => ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e1 : ∀ N : ℕ, ‖((N : ℂ) + 1) ^ (1 - s)‖ = ((N : ℝ) + 1) ^ (1 - s.re) := by
      intro N
      have := norm_cpow_nat N 1 (by positivity) (1 - s)
      push_cast at this; simpa using this
    simp_rw [e1]
    have hN : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have := (tendsto_rpow_neg_atTop (y := s.re - 1) (by linarith)).comp hN
    refine this.congr (fun N => ?_)
    simp only [Function.comp_apply, neg_sub]
  have htB : ∑' n : ℕ, (((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s)) = 1 := by
    have ht := hB.hasSum.tendsto_sum_nat
    simp_rw [hp] at ht
    have hlim : Tendsto (fun N : ℕ => 1 - ((N : ℂ) + 1) ^ (1 - s)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hlim0
    exact tendsto_nhds_unique ht hlim
  unfold F
  calc ∑' n, e n s
      = ∑' n : ℕ, ((1 - s) * ((n : ℂ) + 1) ^ (-s)
          + (((n : ℂ) + 1) ^ (1 - s) - ((n : ℂ) + 2) ^ (1 - s))) := by
        refine tsum_congr (fun n => ?_); simp only [e]; ring
    _ = (1 - s) * riemannZeta s + 1 := by
        rw [hA.tsum_add hB, htB, tsum_mul_left, hz]
        congr 2
        refine tsum_congr (fun n => ?_)
        rw [cpow_neg, one_div]
    _ = 1 + (1 - s) * riemannZeta s := by ring

/- English proof (translation)
Establish `hU : IsOpen {s : ℂ | 0 < s.re}` using `isOpen_lt continuous_const continuous_re`. Establish `hF : AnalyticOnNhd ℂ (fun s => 1 - F s) {s : ℂ | 0 < s.re}`. Rewrite using `[Complex.analyticOnNhd_iff_differentiableOn hU]`. Introduce `z hz`. Conclude with `((F_differentiableAt z hz).const_sub 1).differentiableWithinAt`.

Establish `hZ : AnalyticOnNhd ℂ riemannZeta₁ {s : ℂ | 0 < s.re}` using `fun z _ => differentiable_riemannZeta₁.analyticAt z`. Establish `hpc : IsPreconnected {s : ℂ | 0 < s.re}` using `(convex_halfSpace_re_gt 0).isPreconnected`. Establish `h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re}` using `by simp`. Establish `hev : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] (fun s => 1 - F s)`. Establish `ho : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ)` using `(isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)`.

Use `filter_upwards [ho] with s hs`. Establish `hs1 : s ≠ 1` using `by rintro rfl; simp at hs`. Rewrite using `[F_eq s hs, riemannZeta_eq_inv_sub_mul hs1]`. Establish `hne : s - 1 ≠ 0` using `sub_ne_zero.mpr hs1`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Conclude with `hZ.eqOn_of_preconnected_of_eventuallyEq hF hpc h2 hev h`.
-/
lemma riemannZetaOne_eq_one_sub_of_re_pos (s : ℂ) (h : 0 < s.re) : riemannZeta₁ s = 1 - F s := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const continuous_re
  have hF : AnalyticOnNhd ℂ (fun s => 1 - F s) {s : ℂ | 0 < s.re} := by
    rw [Complex.analyticOnNhd_iff_differentiableOn hU]
    intro z hz
    exact ((F_differentiableAt z hz).const_sub 1).differentiableWithinAt
  have hZ : AnalyticOnNhd ℂ riemannZeta₁ {s : ℂ | 0 < s.re} :=
    fun z _ => differentiable_riemannZeta₁.analyticAt z
  have hpc : IsPreconnected {s : ℂ | 0 < s.re} := (convex_halfSpace_re_gt 0).isPreconnected
  have h2 : (2 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  have hev : riemannZeta₁ =ᶠ[𝓝 (2 : ℂ)] (fun s => 1 - F s) := by
    have ho : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)
    filter_upwards [ho] with s hs
    have hs1 : s ≠ 1 := by rintro rfl; simp at hs
    rw [F_eq s hs, riemannZeta_eq_inv_sub_mul hs1]
    have hne : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    field_simp
    ring
  exact hZ.eqOn_of_preconnected_of_eventuallyEq hF hpc h2 hev h

def er (n : ℕ) (σ : ℝ) : ℝ :=
  (1 - σ) * ((n : ℝ) + 1) ^ (-σ) + ((n : ℝ) + 1) ^ (1 - σ) - ((n : ℝ) + 2) ^ (1 - σ)

/- English proof (translation)
Establish `p1 : (0 : ℝ) ≤ (n : ℝ) + 1` using `by positivity`. Establish `p2 : (0 : ℝ) ≤ (n : ℝ) + 2` using `by positivity`. Simplify using `only [er, e, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_cpow p1, Complex.ofReal_cpow p2, Complex.ofReal_neg, Complex.ofReal_natCast, Complex.ofReal_ofNat]`.
-/
lemma e_ofReal (n : ℕ) (σ : ℝ) : e n σ = (er n σ : ℂ) := by
  have p1 : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have p2 : (0 : ℝ) ≤ (n : ℝ) + 2 := by positivity
  simp only [er, e, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_cpow p1, Complex.ofReal_cpow p2, Complex.ofReal_neg, Complex.ofReal_natCast,
    Complex.ofReal_ofNat]

/- English proof (translation)
Establish `hx0 : 0 < (n : ℝ) + 1` using `by positivity`. Establish `hi : 0 < ((n : ℝ) + 1)⁻¹` using `inv_pos.mpr hx0`. Establish `h2 : (n : ℝ) + 2 = ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)⁻¹)` using `by field_simp; ring`. Establish `hb` using `rpow_one_add_le_one_add_mul_self (s := ((n : ℝ) + 1)⁻¹) (by linarith) (p := 1 - σ) (by linarith) (by linarith)`. Establish `hm : ((n : ℝ) + 2) ^ (1 - σ) = ((n : ℝ) + 1) ^ (1 - σ) * (1 + ((n : ℝ) + 1)⁻¹) ^ (1 - σ)`.

Rewrite using `[h2, Real.mul_rpow hx0.le (by positivity)]`. Establish `hs : ((n : ℝ) + 1) ^ (-σ) = ((n : ℝ) + 1) ^ (1 - σ) * ((n : ℝ) + 1)⁻¹`. Rewrite using `[show -σ = (1 - σ) - 1 by ring, Real.rpow_sub_one hx0.ne', div_eq_mul_inv]`. Establish `hxp : 0 < ((n : ℝ) + 1) ^ (1 - σ)` using `Real.rpow_pos_of_pos hx0 _`. Use `mul_le_mul_of_nonneg_left hb hxp.le` as an intermediate fact.

Unfold `er`. Rewrite using `[hm, hs]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma er_nonneg (n : ℕ) (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) : 0 ≤ er n σ := by
  have hx0 : 0 < (n : ℝ) + 1 := by positivity
  have hi : 0 < ((n : ℝ) + 1)⁻¹ := inv_pos.mpr hx0
  have h2 : (n : ℝ) + 2 = ((n : ℝ) + 1) * (1 + ((n : ℝ) + 1)⁻¹) := by field_simp; ring
  have hb := rpow_one_add_le_one_add_mul_self (s := ((n : ℝ) + 1)⁻¹) (by linarith)
    (p := 1 - σ) (by linarith) (by linarith)
  have hm : ((n : ℝ) + 2) ^ (1 - σ) = ((n : ℝ) + 1) ^ (1 - σ) * (1 + ((n : ℝ) + 1)⁻¹) ^ (1 - σ) := by
    rw [h2, Real.mul_rpow hx0.le (by positivity)]
  have hs : ((n : ℝ) + 1) ^ (-σ) = ((n : ℝ) + 1) ^ (1 - σ) * ((n : ℝ) + 1)⁻¹ := by
    rw [show -σ = (1 - σ) - 1 by ring, Real.rpow_sub_one hx0.ne', div_eq_mul_inv]
  have hxp : 0 < ((n : ℝ) + 1) ^ (1 - σ) := Real.rpow_pos_of_pos hx0 _
  have := mul_le_mul_of_nonneg_left hb hxp.le
  unfold er
  rw [hm, hs]
  nlinarith

/- English proof (translation)
Establish `hy0 : 0 < (n : ℝ) + 2` using `by positivity`. Establish `hyi : ((n : ℝ) + 2)⁻¹ ≤ 1` using `inv_le_one_of_one_le₀ (by have := n.cast_nonneg (α := ℝ); linarith)`. Establish `h2 : (n : ℝ) + 1 = ((n : ℝ) + 2) * (1 + -((n : ℝ) + 2)⁻¹)` using `by field_simp; ring`. Establish `hb` using `rpow_one_add_le_one_add_mul_self (s := -((n : ℝ) + 2)⁻¹) (by linarith) (p := 1 - σ) (by linarith) (by linarith)`. Establish `hpos : 0 ≤ 1 + -((n : ℝ) + 2)⁻¹` using `by linarith`.

Establish `hm : ((n : ℝ) + 1) ^ (1 - σ) = ((n : ℝ) + 2) ^ (1 - σ) * (1 + -((n : ℝ) + 2)⁻¹) ^ (1 - σ)`. Rewrite using `[h2, Real.mul_rpow hy0.le hpos]`. Establish `hs : ((n : ℝ) + 2) ^ (-σ) = ((n : ℝ) + 2) ^ (1 - σ) * ((n : ℝ) + 2)⁻¹`. Rewrite using `[show -σ = (1 - σ) - 1 by ring, Real.rpow_sub_one hy0.ne', div_eq_mul_inv]`. Establish `hyp : 0 < ((n : ℝ) + 2) ^ (1 - σ)` using `Real.rpow_pos_of_pos hy0 _`.

Use `mul_le_mul_of_nonneg_left hb hyp.le` as an intermediate fact. Unfold `er`. Rewrite using `[hm, hs]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma er_le (n : ℕ) (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) :
    er n σ ≤ (1 - σ) * (((n : ℝ) + 1) ^ (-σ) - ((n : ℝ) + 2) ^ (-σ)) := by
  have hy0 : 0 < (n : ℝ) + 2 := by positivity
  have hyi : ((n : ℝ) + 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by have := n.cast_nonneg (α := ℝ); linarith)
  have h2 : (n : ℝ) + 1 = ((n : ℝ) + 2) * (1 + -((n : ℝ) + 2)⁻¹) := by field_simp; ring
  have hb := rpow_one_add_le_one_add_mul_self (s := -((n : ℝ) + 2)⁻¹) (by linarith)
    (p := 1 - σ) (by linarith) (by linarith)
  have hpos : 0 ≤ 1 + -((n : ℝ) + 2)⁻¹ := by linarith
  have hm : ((n : ℝ) + 1) ^ (1 - σ) = ((n : ℝ) + 2) ^ (1 - σ) * (1 + -((n : ℝ) + 2)⁻¹) ^ (1 - σ) := by
    rw [h2, Real.mul_rpow hy0.le hpos]
  have hs : ((n : ℝ) + 2) ^ (-σ) = ((n : ℝ) + 2) ^ (1 - σ) * ((n : ℝ) + 2)⁻¹ := by
    rw [show -σ = (1 - σ) - 1 by ring, Real.rpow_sub_one hy0.ne', div_eq_mul_inv]
  have hyp : 0 < ((n : ℝ) + 2) ^ (1 - σ) := Real.rpow_pos_of_pos hy0 _
  have := mul_le_mul_of_nonneg_left hb hyp.le
  unfold er
  rw [hm, hs]
  nlinarith

/- English proof (translation)
Use `Real.tsum_le_of_sum_range_le (fun n => er_nonneg n σ h0 h1) (fun N => ?_)` and prove the remaining obligations. Set `a : ℕ → ℝ` to `fun i => ((i : ℝ) + 1) ^ (-σ)`. Establish `ha : ∀ i : ℕ, a (i + 1) = ((i : ℝ) + 2) ^ (-σ)`. Introduce `i`. Simplify using `only [a]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[ha]`. Conclude with `er_le i σ h0 h1`. Use `_ = (1 - σ) * (a 0 - a N) := by rw [← Finset.mul_sum, Finset.sum_range_sub']`. Use `_ ≤ 1 - σ := by`. Establish `: 0 ≤ a N` using `by simp only [a]; positivity`.

Establish `ha0 : a 0 = 1` using `by simp [a]`. Rewrite using `[ha0]`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma tsum_er_le (σ : ℝ) (h0 : 0 < σ) (h1 : σ < 1) : ∑' n, er n σ ≤ 1 - σ := by
  refine Real.tsum_le_of_sum_range_le (fun n => er_nonneg n σ h0 h1) (fun N => ?_)
  let a : ℕ → ℝ := fun i => ((i : ℝ) + 1) ^ (-σ)
  have ha : ∀ i : ℕ, a (i + 1) = ((i : ℝ) + 2) ^ (-σ) := by
    intro i; simp only [a]; congr 1; push_cast; ring
  calc ∑ i ∈ Finset.range N, er i σ ≤ ∑ i ∈ Finset.range N, (1 - σ) * (a i - a (i + 1)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [ha]; exact er_le i σ h0 h1
    _ = (1 - σ) * (a 0 - a N) := by rw [← Finset.mul_sum, Finset.sum_range_sub']
    _ ≤ 1 - σ := by
        have : 0 ≤ a N := by simp only [a]; positivity
        have ha0 : a 0 = 1 := by simp [a]
        rw [ha0]; nlinarith

end ZRN

open ZRN in
/- English proof (translation)
Introduce `σ h0 h1`. Establish `hσ1 : (σ : ℂ) ≠ 1`. Introduce `h`. Use `congrArg Complex.re h` as an intermediate fact. Simplify using `at this`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[riemannZeta_eq_inv_sub_mul hσ1]`. Use `mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hσ1)) ?_` and prove the remaining obligations. Rewrite using `[riemannZetaOne_eq_one_sub_of_re_pos _ (by simpa using h0), F]`. Repeatedly rewrite using `[e_ofReal]`.

Rewrite using `[← Complex.ofReal_tsum]`. Use `tsum_er_le σ h0 h1` as an intermediate fact. Introduce `h`. Establish `h'` using `congrArg Complex.re h`. Simplify using `at h'`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem zetaRealNonvanish : ZetaRealNonvanish := by
  intro σ h0 h1
  have hσ1 : (σ : ℂ) ≠ 1 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  rw [riemannZeta_eq_inv_sub_mul hσ1]
  refine mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr hσ1)) ?_
  rw [riemannZetaOne_eq_one_sub_of_re_pos _ (by simpa using h0), F]
  simp_rw [e_ofReal]
  rw [← Complex.ofReal_tsum]
  have := tsum_er_le σ h0 h1
  intro h
  have h' := congrArg Complex.re h
  simp at h'
  linarith

end Formalism
