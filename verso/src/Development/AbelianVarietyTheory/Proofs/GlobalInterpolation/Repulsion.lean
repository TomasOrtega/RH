import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IteratedDerivLogDerivDirichletLViaNearbyZeros
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumIccThreeQuartersPowLe
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.Repulsion

/- English proof (translation)
Establish `han : AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ)`. Apply `DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton` to reduce the goal to its premises. Introduce `z hz`. Conclude with `(differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt`. Establish `hpre : IsPreconnected ({1}ᶜ : Set ℂ)` using `(isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected`.

Establish `h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ)` using `by norm_num`. Establish `hne : LFunction χ 2 ≠ 0` using `LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)`. Establish `h2o : analyticOrderAt (LFunction χ) 2 ≠ ⊤`. Rewrite using `[(han 2 h2).analyticOrderAt_eq_zero.2 hne]`. Simplify using the standard rewrite rules.

Establish `htop : analyticOrderAt (LFunction χ) w ≠ ⊤` using `han.analyticOrderAt_ne_top_of_isPreconnected hpre h2 hw h2o`. Establish `hz : analyticOrderAt (LFunction χ) w ≠ 0`. Rewrite using `[Ne, (han w hw).analyticOrderAt_eq_zero]`. Simplify using `using h0`. Unfold `ord analyticOrderNatAt`.

Rewrite using `[Nat.one_le_iff_ne_zero]`. Introduce `h`. Break down `ENat.toNat_eq_zero.1 h with h | h` into its components or cases. Conclude with `hz h`. Conclude with `htop h`.
-/
theorem one_le_ord {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {w : ℂ} (hw : w ≠ 1)
    (h0 : LFunction χ w = 0) : 1 ≤ ord χ w := by
  have han : AnalyticOnNhd ℂ (LFunction χ) ({1}ᶜ : Set ℂ) := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro z hz
    exact (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
  have hpre : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  have hne : LFunction χ 2 ≠ 0 :=
    LFunction_ne_zero_of_one_le_re χ (Or.inr (by norm_num)) (by norm_num)
  have h2o : analyticOrderAt (LFunction χ) 2 ≠ ⊤ := by
    rw [(han 2 h2).analyticOrderAt_eq_zero.2 hne]; simp
  have htop : analyticOrderAt (LFunction χ) w ≠ ⊤ :=
    han.analyticOrderAt_ne_top_of_isPreconnected hpre h2 hw h2o
  have hz : analyticOrderAt (LFunction χ) w ≠ 0 := by
    rw [Ne, (han w hw).analyticOrderAt_eq_zero]; simpa using h0
  unfold ord analyticOrderNatAt
  rw [Nat.one_le_iff_ne_zero]
  intro h
  rcases ENat.toNat_eq_zero.1 h with h | h
  · exact hz h
  · exact htop h

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b)` using `by ring`. Establish `hbn : ‖b ^ n‖ ≤ 1` using `by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb`.

Rewrite using `[e]`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul, norm_mul]`. Establish `h1 : ‖a‖ * ‖a ^ n - b ^ n‖ ≤ ‖a ^ n - b ^ n‖` using `mul_le_of_le_one_left (norm_nonneg _) ha`. Establish `h2 : ‖b ^ n‖ * ‖a - b‖ ≤ ‖a - b‖` using `mul_le_of_le_one_left (norm_nonneg _) hbn`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_pow_sub_le {a b : ℂ} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (j : ℕ) :
    ‖a ^ j - b ^ j‖ ≤ j * ‖a - b‖ := by
  induction j with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by ring
    have hbn : ‖b ^ n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hb
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖a‖ * ‖a ^ n - b ^ n‖ ≤ ‖a ^ n - b ^ n‖ := mul_le_of_le_one_left (norm_nonneg _) ha
    have h2 : ‖b ^ n‖ * ‖a - b‖ ≤ ‖a - b‖ := mul_le_of_le_one_left (norm_nonneg _) hbn
    push_cast
    linarith

/- English proof (translation)
Establish `h1 : 1 ≤ ‖(2 : ℂ) + t * I - 1‖`. Use `le_trans ?_ (Complex.re_le_norm _)` and prove the remaining obligations. Simplify using the standard rewrite rules. Evaluate the numerical expressions. Establish `h2 : 1 ≤ ‖(2 : ℂ) + t * I - β‖`.

Use `le_trans ?_ (Complex.re_le_norm _)` and prove the remaining obligations. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion. Establish `n1 : (2 : ℂ) + t * I - 1 ≠ 0` using `by intro h; rw [h] at h1; norm_num at h1`. Establish `n2 : (2 : ℂ) + t * I - β ≠ 0` using `by intro h; rw [h] at h2; norm_num at h2`.

Establish `ha : ‖1 / ((2 : ℂ) + t * I - 1)‖ ≤ 1`. Rewrite using `[norm_div, norm_one]`. Conclude with `div_le_one_of_le₀ h1 (norm_nonneg _)`. Establish `hb : ‖1 / ((2 : ℂ) + t * I - β)‖ ≤ 1`. Rewrite using `[norm_div, norm_one]`.

Conclude with `div_le_one_of_le₀ h2 (norm_nonneg _)`. Rewrite using `[← one_div_pow]`. Use `(norm_pow_sub_le ha hb j).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))` and prove the remaining obligations. Establish `e : 1 / ((2 : ℂ) + t * I - 1) - 1 / ((2 : ℂ) + t * I - β) = ((1 - β : ℝ) : ℂ) * (1 / ((2 : ℂ) + t * I - 1)) * (1 / ((2 : ℂ) + t * I - β))` using `by push_cast; field_simp; ring`. Rewrite using `[e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem pole_pair {β t : ℝ} (hβ : β < 1) (j : ℕ) :
    ‖1 / ((2 : ℂ) + t * I - 1) ^ j - (1 / ((2 : ℂ) + t * I - β)) ^ j‖ ≤ j * (1 - β) := by
  have h1 : 1 ≤ ‖(2 : ℂ) + t * I - 1‖ := by
    refine le_trans ?_ (Complex.re_le_norm _); simp; norm_num
  have h2 : 1 ≤ ‖(2 : ℂ) + t * I - β‖ := by
    refine le_trans ?_ (Complex.re_le_norm _); simp; linarith
  have n1 : (2 : ℂ) + t * I - 1 ≠ 0 := by intro h; rw [h] at h1; norm_num at h1
  have n2 : (2 : ℂ) + t * I - β ≠ 0 := by intro h; rw [h] at h2; norm_num at h2
  have ha : ‖1 / ((2 : ℂ) + t * I - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]; exact div_le_one_of_le₀ h1 (norm_nonneg _)
  have hb : ‖1 / ((2 : ℂ) + t * I - β)‖ ≤ 1 := by
    rw [norm_div, norm_one]; exact div_le_one_of_le₀ h2 (norm_nonneg _)
  rw [← one_div_pow]
  refine (norm_pow_sub_le ha hb j).trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  have e : 1 / ((2 : ℂ) + t * I - 1) - 1 / ((2 : ℂ) + t * I - β) =
      ((1 - β : ℝ) : ℂ) * (1 / ((2 : ℂ) + t * I - 1)) * (1 / ((2 : ℂ) + t * I - β)) := by
    push_cast; field_simp; ring
  rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  calc _ ≤ (1 - β) * 1 * 1 := by gcongr
    _ = _ := by ring

/- English proof (translation)
Establish `h1 : 2 ≤ ‖(2 : ℂ) + t * I - 1‖`. Establish `e : (β : ℂ) - (2 + t * I) = -((2 : ℂ) + t * I - 1) + ((β - 1 : ℝ) : ℂ)` using `by push_cast; ring`. Use `norm_add_le (-((2 : ℂ) + t * I - 1)) ((β - 1 : ℝ) : ℂ)` as an intermediate fact. Rewrite `this` using `[← e, norm_neg, Complex.norm_real, Real.norm_of_nonpos (by linarith)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[norm_div, norm_one, norm_pow]`. Use `gcongr`.
-/
theorem pole_far {β t : ℝ} (hβ : β < 1) (hβ' : 1 / 2 ≤ β) (h : ¬ ‖(β : ℂ) - (2 + t * I)‖ ≤ 3) (j : ℕ) :
    ‖1 / ((2 : ℂ) + t * I - 1) ^ j‖ ≤ 1 / 2 ^ j := by
  have h1 : 2 ≤ ‖(2 : ℂ) + t * I - 1‖ := by
    have e : (β : ℂ) - (2 + t * I) = -((2 : ℂ) + t * I - 1) + ((β - 1 : ℝ) : ℂ) := by push_cast; ring
    have := norm_add_le (-((2 : ℂ) + t * I - 1)) ((β - 1 : ℝ) : ℂ)
    rw [← e, norm_neg, Complex.norm_real, Real.norm_of_nonpos (by linarith)] at this
    linarith
  rw [norm_div, norm_one, norm_pow]
  gcongr

/- English proof (translation)
Establish `hO : (fun n : ℕ => Real.log n ^ (k + 1)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)`. Use `(isLittleO_log_rpow_rpow_atTop ((k + 1 : ℕ) : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)).isBigO` as an intermediate fact. Use `this.comp_tendsto tendsto_natCast_atTop_atTop` as an intermediate fact. Simplify `this` using `only [Function.comp_def, Real.rpow_natCast]`. Establish `hS : Summable fun n : ℕ => Real.log n ^ (k + 1) * (n : ℝ) ^ (-2 : ℝ)`.

Use `summable_of_isBigO_nat (Real.summable_nat_rpow.2 (show (-3 / 2 : ℝ) < -1 by norm_num)) ?_` and prove the remaining obligations. Use `(hO.mul (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) atTop)).congr' EventuallyEq.rfl ?_` and prove the remaining obligations. Use `filter_upwards [eventually_gt_atTop 0] with n hn`. Rewrite using `[← Real.rpow_add (by exact_mod_cast hn)]; norm_num`. Use `Summable.of_norm_bounded hS fun n => ?_` and prove the remaining obligations.

Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Establish `hl : 0 ≤ Real.log n` using `Real.log_natCast_nonneg n`. Rewrite using `[norm_mul, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, norm_div, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg, Real.norm_of_nonneg hl, Complex.norm_natCast]`. Establish `e : (-((2 : ℂ) + t * I)).re = -2` using `by simp`.

Rewrite using `[e, pow_succ']`. Establish `hf : (1 : ℝ) ≤ k.factorial` using `by exact_mod_cast k.factorial_pos`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation. Conclude with `div_le_self (by positivity) hf`.
-/
theorem summable_der (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (k : ℕ) (t : ℝ) :
    Summable fun n : ℕ => ((Λ n : ℝ) : ℂ) * c n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) *
      (n : ℂ) ^ (-((2 : ℂ) + t * I)) := by
  have hO : (fun n : ℕ => Real.log n ^ (k + 1)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ) := by
    have := (isLittleO_log_rpow_rpow_atTop ((k + 1 : ℕ) : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num)).isBigO
    have := this.comp_tendsto tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, Real.rpow_natCast] using this
  have hS : Summable fun n : ℕ => Real.log n ^ (k + 1) * (n : ℝ) ^ (-2 : ℝ) := by
    refine summable_of_isBigO_nat (Real.summable_nat_rpow.2 (show (-3 / 2 : ℝ) < -1 by norm_num)) ?_
    refine (hO.mul (Asymptotics.isBigO_refl (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) atTop)).congr' EventuallyEq.rfl ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [← Real.rpow_add (by exact_mod_cast hn)]; norm_num
  refine Summable.of_norm_bounded hS fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn, norm_div, norm_pow,
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg,
    Real.norm_of_nonneg hl, Complex.norm_natCast]
  have e : (-((2 : ℂ) + t * I)).re = -2 := by simp
  rw [e, pow_succ']
  have hf : (1 : ℝ) ≤ k.factorial := by exact_mod_cast k.factorial_pos
  gcongr
  · calc Λ n * ‖c n‖ ≤ Real.log n * 1 := by gcongr; exacts [vonMangoldt_le_log, hc n]
      _ = _ := mul_one _
  · exact div_le_self (by positivity) hf

/- English proof (translation)
Establish `s1` using `summable_der _ (fun n : ℕ => (1 : DirichletCharacter ℂ q).norm_le_one (n : ZMod q)) k 0`. Establish `s2` using `summable_der _ (fun n : ℕ => χ₁.norm_le_one (n : ZMod q)) k 0`. Establish `s3` using `summable_der _ (fun n : ℕ => χ.norm_le_one (n : ZMod q)) k t`. Establish `s4` using `summable_der _ (fun n : ℕ => (χ * χ₁).norm_le_one (n : ZMod q)) k t`. Unfold `derSeries`.

Rewrite using `[← s1.tsum_add s2, ← (s1.add s2).tsum_add s3, ← ((s1.add s2).add s3).tsum_add s4, Complex.re_tsum (((s1.add s2).add s3).add s4)]`. Use `tsum_nonneg fun n => ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using the standard rewrite rules. Distinguish the cases in `hu : IsUnit (n : ZMod q)`.

Use `swap`. Simplify using `[MulChar.map_nonunit _ hu]`. Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `e1 : (n : ℂ) ^ (-((2 : ℂ) + t * I)) = (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I) : ℂ)`. Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, ← Complex.cpow_add _ _ hn']`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e0 : (n : ℂ) ^ (-((2 : ℂ) + (0 : ℝ) * I)) = (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `set u : ℂ := χ n * (n : ℂ) ^ (-(t * I) : ℂ) with hudef`. Establish `hu1 : ‖u‖ ≤ 1`.

Rewrite using `[hudef, norm_mul, Complex.norm_natCast_cpow_of_pos hn]`. Simplify using `using χ.norm_le_one (n : ZMod q)`. Establish `hre : 0 ≤ 1 + u.re` using `by have := (Complex.abs_re_le_norm u).trans hu1; linarith [(abs_le.1 this).1]`. Establish `hsq : χ₁ n ^ 2 = 1`. Rewrite using `[← MulChar.pow_apply' _ two_ne_zero, h, MulChar.one_apply hu]`.

Use `set A : ℝ := Λ n * (Real.log n ^ k / k.factorial) * (n : ℝ) ^ (-2 : ℝ) with hA`. Establish `hA0 : 0 ≤ A`. Use `Real.log_natCast_nonneg n` as an intermediate fact. Use `vonMangoldt_nonneg (n := n)` as an intermediate fact. Check the signs of the components of the expression.

Rewrite using `[e1, e0, MulChar.one_apply hu, MulChar.mul_apply]`. Establish `key : ∀ ε : ℝ, χ₁ n = ε → 0 ≤ 1 + ε → 0 ≤ (((Λ n : ℝ) : ℂ) * 1 * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) + ((Λ n : ℝ) : ℂ) * χ₁ n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) + ((Λ n : ℝ) : ℂ) * χ n * ((Real.log …`. Introduce `ε hε h0`. Establish `: ((Λ n : ℝ) : ℂ) * 1 * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) + ((Λ n : ℝ) : ℂ) * χ₁ n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) + ((Λ n : ℝ) : ℂ) * χ n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * ((((n …`. Rewrite using `[hε, hA, hudef]`.

Simplify using `only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.re_ofReal_mul, Complex.add_re, Complex.one_re]`. Check the signs of the components of the expression. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 (hsq.trans (one_pow 2).symm) with h1 | h1` into its components or cases.

Conclude with `key 1 (by simpa using h1) (by norm_num)`. Conclude with `key (-1) (by simpa using h1) (by norm_num)`.
-/
theorem der_pos {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (h : χ₁ ^ 2 = 1) (k : ℕ) (t : ℝ) :
    0 ≤ (derSeries (fun n : ℕ => (1 : DirichletCharacter ℂ q) (n : ZMod q)) k (2 + (0 : ℝ) * I) +
      derSeries (fun n : ℕ => χ₁ (n : ZMod q)) k (2 + (0 : ℝ) * I) +
      derSeries (fun n : ℕ => χ (n : ZMod q)) k (2 + t * I) +
      derSeries (fun n : ℕ => (χ * χ₁) (n : ZMod q)) k (2 + t * I)).re := by
  have s1 := summable_der _ (fun n : ℕ => (1 : DirichletCharacter ℂ q).norm_le_one (n : ZMod q)) k 0
  have s2 := summable_der _ (fun n : ℕ => χ₁.norm_le_one (n : ZMod q)) k 0
  have s3 := summable_der _ (fun n : ℕ => χ.norm_le_one (n : ZMod q)) k t
  have s4 := summable_der _ (fun n : ℕ => (χ * χ₁).norm_le_one (n : ZMod q)) k t
  unfold derSeries
  rw [← s1.tsum_add s2, ← (s1.add s2).tsum_add s3, ← ((s1.add s2).add s3).tsum_add s4,
    Complex.re_tsum (((s1.add s2).add s3).add s4)]
  refine tsum_nonneg fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  by_cases hu : IsUnit (n : ZMod q)
  swap
  · simp [MulChar.map_nonunit _ hu]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have e1 : (n : ℂ) ^ (-((2 : ℂ) + t * I)) = (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast, ← Complex.cpow_add _ _ hn']
    congr 1; push_cast; ring
  have e0 : (n : ℂ) ^ (-((2 : ℂ) + (0 : ℝ) * I)) = (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
    congr 1; push_cast; ring
  set u : ℂ := χ n * (n : ℂ) ^ (-(t * I) : ℂ) with hudef
  have hu1 : ‖u‖ ≤ 1 := by
    rw [hudef, norm_mul, Complex.norm_natCast_cpow_of_pos hn]
    simpa using χ.norm_le_one (n : ZMod q)
  have hre : 0 ≤ 1 + u.re := by have := (Complex.abs_re_le_norm u).trans hu1; linarith [(abs_le.1 this).1]
  have hsq : χ₁ n ^ 2 = 1 := by
    rw [← MulChar.pow_apply' _ two_ne_zero, h, MulChar.one_apply hu]
  set A : ℝ := Λ n * (Real.log n ^ k / k.factorial) * (n : ℝ) ^ (-2 : ℝ) with hA
  have hA0 : 0 ≤ A := by
    have := Real.log_natCast_nonneg n
    have := vonMangoldt_nonneg (n := n)
    positivity
  rw [e1, e0, MulChar.one_apply hu, MulChar.mul_apply]
  have key : ∀ ε : ℝ, χ₁ n = ε → 0 ≤ 1 + ε → 0 ≤ (((Λ n : ℝ) : ℂ) * 1 * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) +
      ((Λ n : ℝ) : ℂ) * χ₁ n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) +
      ((Λ n : ℝ) : ℂ) * χ n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * ((((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I) : ℂ)) +
      ((Λ n : ℝ) : ℂ) * (χ n * χ₁ n) * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * ((((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I) : ℂ))).re := by
    intro ε hε h0
    have : ((Λ n : ℝ) : ℂ) * 1 * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) +
      ((Λ n : ℝ) : ℂ) * χ₁ n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * (((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) +
      ((Λ n : ℝ) : ℂ) * χ n * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * ((((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I) : ℂ)) +
      ((Λ n : ℝ) : ℂ) * (χ n * χ₁ n) * ((Real.log n : ℂ) ^ k / (k.factorial : ℂ)) * ((((n : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) * (n : ℂ) ^ (-(t * I) : ℂ)) = ((A * (1 + ε) : ℝ) : ℂ) * (1 + u) := by
      rw [hε, hA, hudef]; simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_one]; ring
    rw [this, Complex.re_ofReal_mul, Complex.add_re, Complex.one_re]
    positivity
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hsq.trans (one_pow 2).symm) with h1 | h1
  · exact key 1 (by simpa using h1) (by norm_num)
  · exact key (-1) (by simpa using h1) (by norm_num)

noncomputable def powSum (W : Multiset ℂ) (t : ℝ) (j : ℕ) : ℂ :=
  (W.map fun w => (1 / ((2 : ℂ) + t * I - w)) ^ j).sum

/- English proof (translation)
Take `⟨C, hC, H⟩` from `GlobalTheory.LogDerivHigher.main`. Use `⟨C, hC, fun q _ χ t L hL => ?_⟩` and prove the remaining obligations. Take `⟨hfin, hsum, -⟩` from `H q χ 2 t 0 (by norm_num) le_rfl`. Establish `hCL : C * Real.log (q * (|t| + 2)) ≤ C * L` using `by gcongr`. Use `⟨∑ w ∈ hfin.toFinset, Multiset.replicate (ord χ w) w, fun w h1 h2 h3 => ?_, ?_, fun k => ?_⟩` and prove the remaining obligations.

Establish `hw : w ∈ hfin.toFinset`. Rewrite using `[Set.Finite.mem_toFinset]`. Conclude with `⟨h1, Or.inr h2, h3⟩`. Rewrite using `[Multiset.count_sum', Finset.sum_eq_single_of_mem w hw]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[Multiset.count_replicate, if_neg hb]`. Rewrite `hsum` using `[finsum_mem_eq_finite_toFinset_sum _ hfin]`. Rewrite using `[Multiset.card_sum]`. Simplify using `only [Multiset.card_replicate]`.

Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨-, -, h⟩` from `H q χ 2 t k (by norm_num) le_rfl`. Rewrite `h` using `[finsum_mem_eq_finite_toFinset_sum _ hfin]`. Establish `e : powSum (∑ w ∈ hfin.toFinset, Multiset.replicate (ord χ w) w) t (k + 1) = ∑ w ∈ hfin.toFinset, (ord χ w : ℂ) / (((2 : ℝ) : ℂ) + t * I - w) ^ (k + 1)`.

Unfold `powSum`. Proceed by induction on `hfin.toFinset using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add, Multiset.sum_add, ih]`.

Simplify using `[div_eq_mul_inv]`. Rewrite using `[e]`. Establish `h'` using `(Complex.re_le_norm _).trans h`. Rewrite `h'` using `[Complex.add_re, Complex.sub_re]`. Establish `e2 : 2 * C * L / 2 ^ (k + 1) = C * L / 2 ^ k` using `by rw [pow_succ]; field_simp`.

Establish `h3 : C * Real.log (q * (|t| + 2)) / 2 ^ k ≤ C * L / 2 ^ k` using `by gcongr`. Simplify using `only [Complex.ofReal_ofNat] at h' ⊢`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_list : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t L : ℝ),
    Real.log (q * (|t| + 2)) ≤ L → ∃ W : Multiset ℂ,
      (∀ w : ℂ, ‖w - (2 + t * I)‖ ≤ 3 → w ≠ 1 → LFunction χ w = 0 → W.count w = ord χ w) ∧
      (W.card : ℝ) ≤ C * L ∧ ∀ k : ℕ,
        (derSeries (fun n : ℕ => χ (n : ZMod q)) k (2 + t * I)).re + (powSum W t (k + 1)).re ≤
          (if χ = 1 then 1 / ((2 : ℂ) + t * I - 1) ^ (k + 1) else 0).re + 2 * C * L / 2 ^ (k + 1) := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.LogDerivHigher.main
  refine ⟨C, hC, fun q _ χ t L hL => ?_⟩
  obtain ⟨hfin, hsum, -⟩ := H q χ 2 t 0 (by norm_num) le_rfl
  have hCL : C * Real.log (q * (|t| + 2)) ≤ C * L := by gcongr
  refine ⟨∑ w ∈ hfin.toFinset, Multiset.replicate (ord χ w) w, fun w h1 h2 h3 => ?_, ?_, fun k => ?_⟩
  · have hw : w ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]; exact ⟨h1, Or.inr h2, h3⟩
    rw [Multiset.count_sum', Finset.sum_eq_single_of_mem w hw]
    · simp
    · intro b _ hb
      rw [Multiset.count_replicate, if_neg hb]
  · rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at hsum
    rw [Multiset.card_sum]
    simp only [Multiset.card_replicate]
    push_cast
    linarith
  · obtain ⟨-, -, h⟩ := H q χ 2 t k (by norm_num) le_rfl
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin] at h
    have e : powSum (∑ w ∈ hfin.toFinset, Multiset.replicate (ord χ w) w) t (k + 1) =
        ∑ w ∈ hfin.toFinset, (ord χ w : ℂ) / (((2 : ℝ) : ℂ) + t * I - w) ^ (k + 1) := by
      unfold powSum
      induction hfin.toFinset using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, Multiset.map_add, Multiset.sum_add, ih]
        simp [div_eq_mul_inv]
    rw [e]
    have h' := (Complex.re_le_norm _).trans h
    rw [Complex.add_re, Complex.sub_re] at h'
    have e2 : 2 * C * L / 2 ^ (k + 1) = C * L / 2 ^ k := by rw [pow_succ]; field_simp
    have h3 : C * Real.log (q * (|t| + 2)) / 2 ^ k ≤ C * L / 2 ^ k := by gcongr
    simp only [Complex.ofReal_ofNat] at h' ⊢
    linarith

/- English proof (translation)
Distinguish the cases in `hd : ‖(β : ℂ) - (2 + t * I)‖ ≤ 3`. Establish `hm` using `h hd`. Use `⟨W.erase β, Multiset.card_erase_le, fun w hw hc => ?_, fun j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hwβ : w = β`. Substitute `hwβ` using the available equality.

Establish `h2` using `hc.resolve_left (by simp)`. Rewrite using `[← Multiset.one_le_count_iff_mem, Multiset.count_erase_self]`. Use linear arithmetic over natural numbers and integers. Conclude with `(Multiset.mem_erase_of_ne hwβ).2 hw`. Establish `e : powSum W t j = (1 / ((2 : ℂ) + t * I - β)) ^ j + powSum (W.erase β) t j` using `by conv_lhs => rw [← Multiset.cons_erase hm]`.

Unfold `powSum`. Rewrite using `[Multiset.map_cons, Multiset.sum_cons]`. Establish `h1` using `(Complex.re_le_norm _).trans (pole_pair (t := t) hβ j)`. Rewrite `h1` using `[Complex.sub_re]`. Rewrite using `[e, Complex.add_re]`.

Establish `: (0 : ℝ) ≤ 1 / 2 ^ j` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨W, le_rfl, fun w hw _ => hw, fun j => ?_⟩` and prove the remaining obligations. Establish `h1` using `(Complex.re_le_norm _).trans (pole_far hβ hβ' hd j)`. Establish `: (0 : ℝ) ≤ j * (1 - β)` using `by have : 0 ≤ 1 - β := by linarith`.

Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_erase {β : ℝ} (hβ : β < 1) (hβ' : 1 / 2 ≤ β) (W : Multiset ℂ) (t : ℝ)
    (h : ‖(β : ℂ) - (2 + t * I)‖ ≤ 3 → (β : ℂ) ∈ W) : ∃ W' : Multiset ℂ, W'.card ≤ W.card ∧
      (∀ w ∈ W, w ≠ β ∨ 2 ≤ W.count w → w ∈ W') ∧ ∀ j : ℕ,
        (powSum W' t j).re + (1 / ((2 : ℂ) + t * I - 1) ^ j).re ≤
          (powSum W t j).re + j * (1 - β) + 1 / 2 ^ j := by
  by_cases hd : ‖(β : ℂ) - (2 + t * I)‖ ≤ 3
  · have hm := h hd
    refine ⟨W.erase β, Multiset.card_erase_le, fun w hw hc => ?_, fun j => ?_⟩
    · by_cases hwβ : w = β
      · subst hwβ
        have h2 := hc.resolve_left (by simp)
        rw [← Multiset.one_le_count_iff_mem, Multiset.count_erase_self]; omega
      · exact (Multiset.mem_erase_of_ne hwβ).2 hw
    · have e : powSum W t j = (1 / ((2 : ℂ) + t * I - β)) ^ j + powSum (W.erase β) t j := by
        conv_lhs => rw [← Multiset.cons_erase hm]
        unfold powSum
        rw [Multiset.map_cons, Multiset.sum_cons]
      have h1 := (Complex.re_le_norm _).trans (pole_pair (t := t) hβ j)
      rw [Complex.sub_re] at h1
      rw [e, Complex.add_re]
      have : (0 : ℝ) ≤ 1 / 2 ^ j := by positivity
      linarith
  · refine ⟨W, le_rfl, fun w hw _ => hw, fun j => ?_⟩
    have h1 := (Complex.re_le_norm _).trans (pole_far hβ hβ' hd j)
    have : (0 : ℝ) ≤ j * (1 - β) := by have : 0 ≤ 1 - β := by linarith
                                       positivity
    linarith

/- English proof (translation)
Take `⟨C, hC, H⟩` from `GlobalTheory.powerSum_repulsion`. Use `⟨C, hC, fun M z L δ x hz hL hδ hx hx' hn hc hs => ?_⟩` and prove the remaining obligations. Use `H ℂ M.toFinset id (fun y => M.count y) z L δ x (Multiset.mem_toFinset.2 hz) (Multiset.one_le_count_iff_mem.2 hz) hL hδ hx hx' hn ?_ fun j hj => ?_` and prove the remaining obligations. Rewrite `hc` using `[← Multiset.toFinset_sum_count_eq]`. Conclude with `hc` after adjusting the coercions.

Use `hs j hj` as an intermediate fact. Rewrite `this` using `[Finset.sum_multiset_map_count]`. Simplify `this` using `[nsmul_eq_mul]`.
-/
theorem power_step : ∃ C : ℝ, 0 < C ∧ ∀ (M : Multiset ℂ) (z : ℂ) (L δ x : ℝ), z ∈ M → 1 ≤ L → 0 < δ →
    0 ≤ x → x ≤ 1 / 2 → 1 / (1 + x) ≤ ‖z‖ → (M.card : ℝ) ≤ L →
    (∀ j : ℕ, 1 ≤ j → (M.map fun y => y ^ j).sum.re ≤ 2 * j * δ + L / 2 ^ j) →
    Real.log (1 / (C * L * δ)) / (C * L) ≤ x := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.powerSum_repulsion
  refine ⟨C, hC, fun M z L δ x hz hL hδ hx hx' hn hc hs => ?_⟩
  refine H ℂ M.toFinset id (fun y => M.count y) z L δ x (Multiset.mem_toFinset.2 hz)
    (Multiset.one_le_count_iff_mem.2 hz) hL hδ hx hx' hn ?_ fun j hj => ?_
  · rw [← Multiset.toFinset_sum_count_eq] at hc
    exact_mod_cast hc
  · have := hs j hj
    rw [Finset.sum_multiset_map_count] at this
    simpa [nsmul_eq_mul] using this

/- English proof (translation)
Take `⟨C, hC, H⟩` from `exists_list`. Take `⟨D, hD, P⟩` from `power_step`. Use `⟨1 / (D * (8 * C + 4)), by positivity, ?_⟩` and prove the remaining obligations. Introduce `q _ χ₁ χ β L ρ h1 hsq hβ hβ' hz₁ hz hρ hρ' hcase hL`. Use `set t := ρ.im with ht`.

Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast NeZero.pos q`. Establish `hL0 : Real.log (q * (|(0 : ℝ)| + 2)) ≤ L`. Use `le_trans (Real.log_le_log (by positivity) ?_) hL` and prove the remaining obligations. Rewrite using `[abs_zero]`. Conclude with `mul_le_mul_of_nonneg_left (by linarith [abs_nonneg t]) (by linarith)`.

Establish `hLh : 1 / 2 ≤ L`. Use `le_trans ?_ hL0` and prove the remaining obligations. Use `Real.log_two_gt_d9` as an intermediate fact. Use `le_trans (by linarith : (1 : ℝ) / 2 ≤ Real.log 2) (Real.log_le_log (by norm_num) ?_)` and prove the remaining obligations. Rewrite using `[abs_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hβ1 : (β : ℂ) ≠ 1` using `by exact_mod_cast hβ.ne`. Establish `hρ1 : ρ ≠ 1` using `by rintro rfl; simp at hρ'`. Establish `eρ : (2 : ℂ) + t * I - ρ = ((2 - ρ.re : ℝ) : ℂ)`. Apply the tactic sequence `apply Complex.ext <;> simp [ht]`.

Establish `hρd : ‖ρ - (2 + t * I)‖ ≤ 3`. Rewrite using `[norm_sub_rev, eρ, Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith`. Take `⟨W0, -, c0, s0⟩` from `H q 1 0 L hL0`. Take `⟨W1, m1, c1, s1⟩` from `H q χ₁ 0 L hL0`. Take `⟨W2, m2, c2, s2⟩` from `H q χ t L hL`.

Take `⟨W3, m3, c3, s3⟩` from `H q (χ * χ₁) t L hL`. Establish `hρ2 : ρ ∈ W2`. Rewrite using `[← Multiset.one_le_count_iff_mem, m2 ρ hρd hρ1 hz]`. Conclude with `one_le_ord χ hρ1 hz`. Take `⟨V1, d1, -, r1⟩` from `exists_erase hβ hβ' W1 0 fun hd => by`.

Rewrite using `[← Multiset.one_le_count_iff_mem, m1 β hd hβ1 hz₁]`. Conclude with `one_le_ord χ₁ hβ1 hz₁`. Establish `hmul : χ * χ₁ = 1 ↔ χ = χ₁`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `rfl`. Rewrite using `[← sq, hsq]`. Choose the witnesses or unpack the hypotheses as in `⟨V2, V3, d2, d3, hρV, r23⟩ : ∃ V2 V3 : Multiset ℂ, V2.card ≤ W2.card ∧ V3.card ≤ W3.card ∧ ρ ∈ V2 ∧ ∀ j : ℕ, (powSum V2 t j).re + (powSum V3 t j).re + (if χ = 1 then 1 / ((2 : ℂ) + t * I - 1) ^ j else 0).re + (if χ * χ₁ = 1 then 1 / ((2 : ℂ) + t * I - 1) ^ j else 0).re ≤ (powSum …`. Distinguish the cases in `a : χ = 1`.

Substitute `a` using the available equality. Rewrite `m3`, the goal using `[one_mul]`. Take `⟨V, d, -, r⟩` from `exists_erase hβ hβ' W3 t fun hd => by`. Rewrite using `[← Multiset.one_le_count_iff_mem, m3 β hd hβ1 hz₁]`. Conclude with `one_le_ord χ₁ hβ1 hz₁`.

Use `⟨W2, V, le_rfl, d, hρ2, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[if_pos rfl, if_neg h1, Complex.zero_re]`. Combine the linear relations using `[r j]`. Distinguish the cases in `b : χ = χ₁`. Substitute `b` using the available equality.

Take `⟨V, d, m, r⟩` from `exists_erase hβ hβ' W2 t fun hd => by`. Rewrite using `[← Multiset.one_le_count_iff_mem, m2 β hd hβ1 hz₁]`. Conclude with `one_le_ord χ hβ1 hz₁`. Use `⟨V, W3, d, le_rfl, m ρ hρ2 ?_, fun j => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hb : ρ = β`.

Use `right`. Rewrite using `[m2 ρ hρd hρ1 hz, hb]`. Simplify `hcase` using `[hb]`. Conclude with `Or.inl hb`. Rewrite using `[if_neg a, if_pos (hmul.2 rfl), Complex.zero_re]`.

Combine the linear relations using `[r j]`. Use `⟨W2, W3, le_rfl, le_rfl, hρ2, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[if_neg a, if_neg (mt hmul.1 b), Complex.zero_re]`. Establish `: (0 : ℝ) ≤ j * (1 - β)` using `by have : 0 ≤ 1 - β := by linarith`. Check the signs of the components of the expression.

Establish `: (0 : ℝ) ≤ 1 / 2 ^ j` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hCL : 0 ≤ C * L` using `by positivity`. Establish `key` using `P ((W0 + V1).map (fun w => 1 / ((2 : ℂ) + (0 : ℝ) * I - w)) + (V2 + V3).map (fun w => 1 / ((2 : ℂ) + t * I - w))) (1 / ((2 : ℂ) + t * I - ρ)) ((8 * C + 4) * L) (1 - β) (1 - ρ.re) (Multiset.mem_add.2 (Or.inr (Multiset.mem_map_of_mem _ (Multiset.mem_add.2 (Or.inl hρV))))) (by nlina …`. Establish `hL' : 0 < L` using `by linarith`.

Establish `hδ : 0 < 1 - β` using `by linarith`. Use `key using 1` and compare the differences between its conclusion and the goal. Establish `e : 1 / (D * (8 * C + 4)) / ((1 - β) * L) = 1 / (D * ((8 * C + 4) * L) * (1 - β))`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[eρ, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]`. Apply `le_of_eq` to reduce the goal to its premises. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Multiset.card_add, Multiset.card_map]`. Establish `d1' : (V1.card : ℝ) ≤ W1.card` using `by exact_mod_cast d1`. Establish `d2' : (V2.card : ℝ) ≤ W2.card` using `by exact_mod_cast d2`. Establish `d3' : (V3.card : ℝ) ≤ W3.card` using `by exact_mod_cast d3`. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities. Introduce `j hj`. Take `⟨k, rfl⟩ : ∃ k, j = k + 1` from `⟨j - 1, by omega⟩`. Establish `e : (Multiset.map (fun y => y ^ (k + 1)) ((W0 + V1).map (fun w => 1 / ((2 : ℂ) + (0 : ℝ) * I - w)) + (V2 + V3).map (fun w => 1 / ((2 : ℂ) + t * I - w)))).sum = powSum W0 0 (k + 1) + powSum V1 0 (k + 1) + powSum V2 t (k + 1) + powSum V3 t (k + 1)`. Unfold `powSum`.

Simplify using `only [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `hp` using `der_pos χ₁ χ hsq k t`. Establish `a0` using `s0 k`.

Establish `a1` using `s1 k`. Establish `a2` using `s2 k`. Establish `a3` using `s3 k`. Establish `b1` using `r1 (k + 1)`. Establish `b2` using `r23 (k + 1)`.

Rewrite `a0` using `[if_pos rfl]`. Rewrite `a1` using `[if_neg h1, Complex.zero_re]`. Simplify using `only [Complex.add_re] at hp ⊢`. Establish `f : (8 * C + 4) * L / 2 ^ (k + 1) = 4 * (2 * C * L / 2 ^ (k + 1)) + 4 * L * (1 / 2 ^ (k + 1))`. Expand and normalize the polynomial expressions, which then agree.

Establish `g : (1 : ℝ) / 2 ^ (k + 1) * 2 ≤ 4 * L * (1 / 2 ^ (k + 1))`. Rewrite using `[mul_comm]`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem repulsion : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (β L : ℝ) (ρ : ℂ), χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β < 1 → 1 / 2 ≤ β → LFunction χ₁ β = 0 → LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re → ρ.re < 1 → (χ ≠ χ₁ ∨ ρ ≠ β ∨ 2 ≤ ord χ₁ β) → Real.log (q * (|ρ.im| + 2)) ≤ L → c * Real.log (c / ((1 - β) * L)) / L ≤ 1 - ρ.re := by
  obtain ⟨C, hC, H⟩ := exists_list
  obtain ⟨D, hD, P⟩ := power_step
  refine ⟨1 / (D * (8 * C + 4)), by positivity, ?_⟩
  intro q _ χ₁ χ β L ρ h1 hsq hβ hβ' hz₁ hz hρ hρ' hcase hL
  set t := ρ.im with ht
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hL0 : Real.log (q * (|(0 : ℝ)| + 2)) ≤ L := by
    refine le_trans (Real.log_le_log (by positivity) ?_) hL
    rw [abs_zero]
    exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg t]) (by linarith)
  have hLh : 1 / 2 ≤ L := by
    refine le_trans ?_ hL0
    have := Real.log_two_gt_d9
    refine le_trans (by linarith : (1 : ℝ) / 2 ≤ Real.log 2) (Real.log_le_log (by norm_num) ?_)
    rw [abs_zero]; linarith
  have hβ1 : (β : ℂ) ≠ 1 := by exact_mod_cast hβ.ne
  have hρ1 : ρ ≠ 1 := by rintro rfl; simp at hρ'
  have eρ : (2 : ℂ) + t * I - ρ = ((2 - ρ.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [ht]
  have hρd : ‖ρ - (2 + t * I)‖ ≤ 3 := by
    rw [norm_sub_rev, eρ, Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  obtain ⟨W0, -, c0, s0⟩ := H q 1 0 L hL0
  obtain ⟨W1, m1, c1, s1⟩ := H q χ₁ 0 L hL0
  obtain ⟨W2, m2, c2, s2⟩ := H q χ t L hL
  obtain ⟨W3, m3, c3, s3⟩ := H q (χ * χ₁) t L hL
  have hρ2 : ρ ∈ W2 := by
    rw [← Multiset.one_le_count_iff_mem, m2 ρ hρd hρ1 hz]; exact one_le_ord χ hρ1 hz
  obtain ⟨V1, d1, -, r1⟩ := exists_erase hβ hβ' W1 0 fun hd => by
    rw [← Multiset.one_le_count_iff_mem, m1 β hd hβ1 hz₁]; exact one_le_ord χ₁ hβ1 hz₁
  have hmul : χ * χ₁ = 1 ↔ χ = χ₁ := by
    constructor
    · intro h
      calc χ = χ * χ₁ ^ 2 := by rw [hsq, mul_one]
        _ = χ₁ := by rw [sq, ← mul_assoc, h, one_mul]
    · rintro rfl; rw [← sq, hsq]
  obtain ⟨V2, V3, d2, d3, hρV, r23⟩ : ∃ V2 V3 : Multiset ℂ, V2.card ≤ W2.card ∧ V3.card ≤ W3.card ∧
      ρ ∈ V2 ∧ ∀ j : ℕ, (powSum V2 t j).re + (powSum V3 t j).re +
        (if χ = 1 then 1 / ((2 : ℂ) + t * I - 1) ^ j else 0).re +
        (if χ * χ₁ = 1 then 1 / ((2 : ℂ) + t * I - 1) ^ j else 0).re ≤
        (powSum W2 t j).re + (powSum W3 t j).re + j * (1 - β) + 1 / 2 ^ j := by
    by_cases a : χ = 1
    · subst a
      rw [one_mul] at m3 ⊢
      obtain ⟨V, d, -, r⟩ := exists_erase hβ hβ' W3 t fun hd => by
        rw [← Multiset.one_le_count_iff_mem, m3 β hd hβ1 hz₁]; exact one_le_ord χ₁ hβ1 hz₁
      refine ⟨W2, V, le_rfl, d, hρ2, fun j => ?_⟩
      rw [if_pos rfl, if_neg h1, Complex.zero_re]
      linarith [r j]
    by_cases b : χ = χ₁
    · subst b
      obtain ⟨V, d, m, r⟩ := exists_erase hβ hβ' W2 t fun hd => by
        rw [← Multiset.one_le_count_iff_mem, m2 β hd hβ1 hz₁]; exact one_le_ord χ hβ1 hz₁
      refine ⟨V, W3, d, le_rfl, m ρ hρ2 ?_, fun j => ?_⟩
      · by_cases hb : ρ = β
        · right
          rw [m2 ρ hρd hρ1 hz, hb]
          simpa [hb] using hcase
        · exact Or.inl hb
      · rw [if_neg a, if_pos (hmul.2 rfl), Complex.zero_re]
        linarith [r j]
    · refine ⟨W2, W3, le_rfl, le_rfl, hρ2, fun j => ?_⟩
      rw [if_neg a, if_neg (mt hmul.1 b), Complex.zero_re]
      have : (0 : ℝ) ≤ j * (1 - β) := by have : 0 ≤ 1 - β := by linarith
                                         positivity
      have : (0 : ℝ) ≤ 1 / 2 ^ j := by positivity
      linarith
  have hCL : 0 ≤ C * L := by positivity
  have key := P ((W0 + V1).map (fun w => 1 / ((2 : ℂ) + (0 : ℝ) * I - w)) +
      (V2 + V3).map (fun w => 1 / ((2 : ℂ) + t * I - w))) (1 / ((2 : ℂ) + t * I - ρ))
      ((8 * C + 4) * L) (1 - β) (1 - ρ.re)
      (Multiset.mem_add.2 (Or.inr (Multiset.mem_map_of_mem _ (Multiset.mem_add.2 (Or.inl hρV)))))
      (by nlinarith) (by linarith) (by linarith) (by linarith) ?_ ?_ ?_
  · have hL' : 0 < L := by linarith
    have hδ : 0 < 1 - β := by linarith
    convert key using 1
    have e : 1 / (D * (8 * C + 4)) / ((1 - β) * L) = 1 / (D * ((8 * C + 4) * L) * (1 - β)) := by
      field_simp
    rw [e]; field_simp
  · rw [eρ, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    apply le_of_eq; congr 1; ring
  · simp only [Multiset.card_add, Multiset.card_map]
    have d1' : (V1.card : ℝ) ≤ W1.card := by exact_mod_cast d1
    have d2' : (V2.card : ℝ) ≤ W2.card := by exact_mod_cast d2
    have d3' : (V3.card : ℝ) ≤ W3.card := by exact_mod_cast d3
    push_cast
    nlinarith
  · intro j hj
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have e : (Multiset.map (fun y => y ^ (k + 1)) ((W0 + V1).map (fun w => 1 / ((2 : ℂ) + (0 : ℝ) * I - w)) +
        (V2 + V3).map (fun w => 1 / ((2 : ℂ) + t * I - w)))).sum =
        powSum W0 0 (k + 1) + powSum V1 0 (k + 1) + powSum V2 t (k + 1) + powSum V3 t (k + 1) := by
      unfold powSum
      simp only [Multiset.map_add, Multiset.sum_add, Multiset.map_map, Function.comp_def]
      ring
    rw [e]
    have hp := der_pos χ₁ χ hsq k t
    have a0 := s0 k
    have a1 := s1 k
    have a2 := s2 k
    have a3 := s3 k
    have b1 := r1 (k + 1)
    have b2 := r23 (k + 1)
    rw [if_pos rfl] at a0
    rw [if_neg h1, Complex.zero_re] at a1
    simp only [Complex.add_re] at hp ⊢
    have f : (8 * C + 4) * L / 2 ^ (k + 1) = 4 * (2 * C * L / 2 ^ (k + 1)) + 4 * L * (1 / 2 ^ (k + 1)) := by
      ring
    have g : (1 : ℝ) / 2 ^ (k + 1) * 2 ≤ 4 * L * (1 / 2 ^ (k + 1)) := by
      rw [mul_comm]; gcongr; linarith
    linarith

end GlobalTheory.Lin.Repulsion
