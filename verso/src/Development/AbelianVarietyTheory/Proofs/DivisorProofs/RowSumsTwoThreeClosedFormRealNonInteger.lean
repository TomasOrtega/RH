import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open Filter Topology

namespace GlobalTheory.WpFam.RowReal

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
/- English proof (translation)
Establish `h : w + m = ((w.re + m : ℝ) : ℂ)` using `Complex.ext (by simp) (by simp [hw])`. Rewrite using `[h, Complex.norm_real, Real.norm_eq_abs, add_comm]`.
-/
private lemma norm_add_intCast_eq_abs_of_im_eq_zero {w : ℂ} (hw : w.im = 0) (m : ℤ) :
    ‖w + m‖ = |(m : ℝ) + w.re| := by
  have h : w + m = ((w.re + m : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw])
  rw [h, Complex.norm_real, Real.norm_eq_abs, add_comm]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
/- English proof (translation)
Establish `hwx : w = ((w.re : ℝ) : ℂ)` using `Complex.ext (by simp) (by simp [hw])`. Establish `hf0 : 0 < Int.fract w.re`. Break down `(Int.fract_nonneg w.re).lt_or_eq with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction.

Apply `hn ⌊w.re⌋` to reduce the goal to its premises. Establish `h2` using `Int.floor_add_fract w.re`. Rewrite `h2` using `[← h, add_zero]`. Conclude with `Complex.ext (by simp [h2]) (by simp [hw])`. Establish `hf1` using `Int.fract_lt_one w.re`.

Use `⟨min (Int.fract w.re) (1 - Int.fract w.re), lt_min hf0 (by linarith), fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[norm_add_intCast_eq_abs_of_im_eq_zero hw m]`. Establish `hx` using `Int.floor_add_fract w.re`. Break down `le_or_gt 0 (⌊w.re⌋ + m) with h | h` into its components or cases. Establish `h' : (0 : ℝ) ≤ ((⌊w.re⌋ + m : ℤ) : ℝ)` using `by exact_mod_cast h`.

Move the coercions through the operations in `at h'`. Rewrite using `[abs_of_nonneg (by linarith)]`. Conclude with `(min_le_left _ _).trans (by linarith)`. Establish `h' : ((⌊w.re⌋ + m : ℤ) : ℝ) ≤ -1` using `by exact_mod_cast (by omega : ⌊w.re⌋ + m ≤ -1)`. Move the coercions through the operations in `at h'`.

Rewrite using `[abs_of_neg (by linarith)]`. Conclude with `(min_le_right _ _).trans (by linarith)`.
-/
private lemma exists_pos_le_norm_add_intCast_of_im_eq_zero {w : ℂ} (hw : w.im = 0) (hn : ∀ n : ℤ, w ≠ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m : ℤ, δ ≤ ‖w + m‖ := by
  have hwx : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw])
  have hf0 : 0 < Int.fract w.re := by
    rcases (Int.fract_nonneg w.re).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hn ⌊w.re⌋
      have h2 := Int.floor_add_fract w.re
      rw [← h, add_zero] at h2
      exact Complex.ext (by simp [h2]) (by simp [hw])
  have hf1 := Int.fract_lt_one w.re
  refine ⟨min (Int.fract w.re) (1 - Int.fract w.re), lt_min hf0 (by linarith), fun m => ?_⟩
  rw [norm_add_intCast_eq_abs_of_im_eq_zero hw m]
  have hx := Int.floor_add_fract w.re
  rcases le_or_gt 0 (⌊w.re⌋ + m) with h | h
  · have h' : (0 : ℝ) ≤ ((⌊w.re⌋ + m : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    rw [abs_of_nonneg (by linarith)]
    exact (min_le_left _ _).trans (by linarith)
  · have h' : ((⌊w.re⌋ + m : ℤ) : ℝ) ≤ -1 := by exact_mod_cast (by omega : ⌊w.re⌋ + m ≤ -1)
    push_cast at h'
    rw [abs_of_neg (by linarith)]
    exact (min_le_right _ _).trans (by linarith)

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
/- English proof (translation)
Take `⟨δ, hδ, hδm⟩` from `exists_pos_le_norm_add_intCast_of_im_eq_zero hw hn`. Establish `hsum : Summable fun m : ℤ => 2 ^ k * (1 / ‖w + m‖ ^ k)`. Use `Summable.mul_left _ ?_` and prove the remaining obligations. Establish `h` using `(Real.summable_one_div_int_add_rpow w.re (k : ℝ)).2 (by exact_mod_cast (by omega : 1 < k))`. Use `h.congr fun m => ?_` and prove the remaining obligations.

Rewrite using `[Real.rpow_natCast, norm_add_intCast_eq_abs_of_im_eq_zero hw m]`. Establish `hlow : ∀ (m : ℤ) (x : ℂ), x ∈ Metric.closedBall w (δ / 2) → ‖w + m‖ / 2 ≤ ‖x + m‖`. Introduce `m x hx`. Establish `hxw : ‖x - w‖ ≤ δ / 2` using `by rw [← dist_eq_norm]; exact hx`. Establish `h1` using `hδm m`.

Establish `h2` using `norm_sub_norm_le (w + m) (x + m)`. Rewrite `h2` using `[show (w + (m : ℂ)) - (x + m) = -(x - w) by ring, norm_neg]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcont : ContinuousOn (fun x : ℂ => ∑' m : ℤ, 1 / (x + (m : ℂ)) ^ k) (Metric.closedBall w (δ / 2))`. Use `continuousOn_tsum (fun m => ?_) hsum (fun m x hx => ?_)` and prove the remaining obligations.

Use `ContinuousOn.div continuousOn_const (by fun_prop) (fun x hx => pow_ne_zero _ ?_)` and prove the remaining obligations. Establish `h1` using `hlow m x hx`. Establish `h2` using `hδm m`. Conclude with `norm_ne_zero_iff.mp (by linarith)`. Establish `hpos : 0 < ‖w + m‖ / 2` using `by linarith [hδm m]`.

Rewrite using `[norm_div, norm_one, norm_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `hcw : ContinuousAt (fun x : ℂ => ∑' m : ℤ, 1 / (x + (m : ℂ)) ^ k) w` using `hcont.continuousAt (Metric.closedBall_mem_nhds w (by linarith))`. Establish `hpath : Tendsto (fun ε : ℝ => w + ε * Complex.I) (𝓝[>] 0) (𝓝 w)`. Establish `hc : Continuous (fun ε : ℝ => w + ε * Complex.I)` using `by fun_prop`.

Establish `h` using `hc.tendsto 0`. Simplify using `only [Complex.ofReal_zero, zero_mul, add_zero] at h`. Conclude with `h.mono_left nhdsWithin_le_nhds`. Use `tendsto_nhds_unique ((hcw.tendsto.comp hpath).congr' ?_) (hG.tendsto.comp hpath)` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`.

Conclude with `hEq _ (by simpa [hw] using hε)`.
-/
private lemma tsum_one_div_add_int_pow_of_real_of_continuousAt {w : ℂ} (hw : w.im = 0)
    (hn : ∀ n : ℤ, w ≠ n) {k : ℕ} (hk : 2 ≤ k) {G : ℂ → ℂ} (hG : ContinuousAt G w)
    (hEq : ∀ z : ℂ, 0 < z.im → ∑' m : ℤ, 1 / (z + m) ^ k = G z) :
    ∑' m : ℤ, 1 / (w + m) ^ k = G w := by
  obtain ⟨δ, hδ, hδm⟩ := exists_pos_le_norm_add_intCast_of_im_eq_zero hw hn
  have hsum : Summable fun m : ℤ => 2 ^ k * (1 / ‖w + m‖ ^ k) := by
    refine Summable.mul_left _ ?_
    have h := (Real.summable_one_div_int_add_rpow w.re (k : ℝ)).2
      (by exact_mod_cast (by omega : 1 < k))
    refine h.congr fun m => ?_
    rw [Real.rpow_natCast, norm_add_intCast_eq_abs_of_im_eq_zero hw m]
  have hlow : ∀ (m : ℤ) (x : ℂ), x ∈ Metric.closedBall w (δ / 2) → ‖w + m‖ / 2 ≤ ‖x + m‖ := by
    intro m x hx
    have hxw : ‖x - w‖ ≤ δ / 2 := by rw [← dist_eq_norm]; exact hx
    have h1 := hδm m
    have h2 := norm_sub_norm_le (w + m) (x + m)
    rw [show (w + (m : ℂ)) - (x + m) = -(x - w) by ring, norm_neg] at h2
    linarith
  have hcont : ContinuousOn (fun x : ℂ => ∑' m : ℤ, 1 / (x + (m : ℂ)) ^ k)
      (Metric.closedBall w (δ / 2)) := by
    refine continuousOn_tsum (fun m => ?_) hsum (fun m x hx => ?_)
    · refine ContinuousOn.div continuousOn_const (by fun_prop) (fun x hx => pow_ne_zero _ ?_)
      have h1 := hlow m x hx
      have h2 := hδm m
      exact norm_ne_zero_iff.mp (by linarith)
    · have hpos : 0 < ‖w + m‖ / 2 := by linarith [hδm m]
      rw [norm_div, norm_one, norm_pow]
      calc 1 / ‖x + m‖ ^ k ≤ 1 / (‖w + m‖ / 2) ^ k :=
            one_div_le_one_div_of_le (pow_pos hpos k) (pow_le_pow_left₀ hpos.le (hlow m x hx) k)
        _ = 2 ^ k * (1 / ‖w + m‖ ^ k) := by rw [div_pow, one_div_div, mul_one_div]
  have hcw : ContinuousAt (fun x : ℂ => ∑' m : ℤ, 1 / (x + (m : ℂ)) ^ k) w :=
    hcont.continuousAt (Metric.closedBall_mem_nhds w (by linarith))
  have hpath : Tendsto (fun ε : ℝ => w + ε * Complex.I) (𝓝[>] 0) (𝓝 w) := by
    have hc : Continuous (fun ε : ℝ => w + ε * Complex.I) := by fun_prop
    have h := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_nhds_unique ((hcw.tendsto.comp hpath).congr' ?_) (hG.tendsto.comp hpath)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hEq _ (by simpa [hw] using hε)

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
/- English proof (translation)
Establish `h` using `EisensteinSeries.qExpansion_identity (k := 1) le_rfl ⟨z, hz⟩`. Establish `hq` using `UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩`. Simplify using `only [UpperHalfPlane.coe_mk] at h hq`. Simplify using `only [Nat.reduceAdd, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h`. Rewrite using `[h, tsum_coe_mul_geometric_of_norm_lt_one hq]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma tsum_one_div_add_int_sq_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    ∑' m : ℤ, 1 / (z + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 *
      (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)
        / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) ^ 2) := by
  have h := EisensteinSeries.qExpansion_identity (k := 1) le_rfl ⟨z, hz⟩
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
  simp only [UpperHalfPlane.coe_mk] at h hq
  simp only [Nat.reduceAdd, pow_one, Nat.factorial_one, Nat.cast_one, div_one] at h
  rw [h, tsum_coe_mul_geometric_of_norm_lt_one hq]
  ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
/- English proof (translation)
Establish `hne : 1 - r ≠ 0`. Introduce `h`. Establish `: r = 1` using `by linear_combination -h`. Rewrite `hr` using `[this, norm_one]`. Conclude with `lt_irrefl _ hr`.

Establish `hS : Summable fun n : ℕ => (n : ℂ) ^ 2 * r ^ n` using `summable_pow_mul_geometric_of_norm_lt_one 2 hr`. Establish `hS1 : Summable fun n : ℕ => (n : ℂ) * r ^ n`. Simplify using `using summable_pow_mul_geometric_of_norm_lt_one 1 hr`. Establish `hG : Summable fun n : ℕ => r ^ n` using `summable_geometric_of_norm_lt_one hr`. Establish `h1` using `tsum_coe_mul_geometric_of_norm_lt_one hr`.

Establish `hg` using `tsum_geometric_of_norm_lt_one hr`. Establish `hsplit` using `hS.tsum_eq_zero_add`. Establish `hshift : (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 2 * r ^ (n + 1)) = fun n : ℕ => r * ((n : ℂ) ^ 2 * r ^ n) + 2 * r * ((n : ℂ) * r ^ n) + r * r ^ n`. Use function extensionality and compare the values at `n`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `hsplit` using `[hshift, ((hS.mul_left r).add (hS1.mul_left (2 * r))).tsum_add (hG.mul_left r), (hS.mul_left r).tsum_add (hS1.mul_left (2 * r)), tsum_mul_left, tsum_mul_left, tsum_mul_left, h1, hg]`. Simplify using `only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero, mul_one, zero_add] at hsplit`. Use `set S := ∑' n : ℕ, (n : ℂ) ^ 2 * r ^ n`. Establish `e1 : r / (1 - r) ^ 2 * (1 - r) ^ 2 = r` using `div_mul_cancel₀ _ (pow_ne_zero 2 hne)`.

Establish `e2 : (1 - r)⁻¹ * (1 - r) = 1` using `inv_mul_cancel₀ hne`. Rewrite using `[eq_div_iff (pow_ne_zero 3 hne)]`. Take the linear combination `(1 - r) ^ 2 * hsplit + 2 * r * e1 + r * (1 - r) * e2`.
-/
private lemma tsum_sq_mul_geometric_of_norm_lt_one {r : ℂ} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, (n : ℂ) ^ 2 * r ^ n = r * (1 + r) / (1 - r) ^ 3 := by
  have hne : 1 - r ≠ 0 := by
    intro h
    have : r = 1 := by linear_combination -h
    rw [this, norm_one] at hr
    exact lt_irrefl _ hr
  have hS : Summable fun n : ℕ => (n : ℂ) ^ 2 * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one 2 hr
  have hS1 : Summable fun n : ℕ => (n : ℂ) * r ^ n := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have hG : Summable fun n : ℕ => r ^ n := summable_geometric_of_norm_lt_one hr
  have h1 := tsum_coe_mul_geometric_of_norm_lt_one hr
  have hg := tsum_geometric_of_norm_lt_one hr
  have hsplit := hS.tsum_eq_zero_add
  have hshift : (fun n : ℕ => ((n + 1 : ℕ) : ℂ) ^ 2 * r ^ (n + 1))
      = fun n : ℕ => r * ((n : ℂ) ^ 2 * r ^ n) + 2 * r * ((n : ℂ) * r ^ n) + r * r ^ n := by
    funext n
    push_cast
    ring
  rw [hshift, ((hS.mul_left r).add (hS1.mul_left (2 * r))).tsum_add (hG.mul_left r),
    (hS.mul_left r).tsum_add (hS1.mul_left (2 * r)), tsum_mul_left, tsum_mul_left, tsum_mul_left,
    h1, hg] at hsplit
  simp only [Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, pow_zero,
    mul_one, zero_add] at hsplit
  set S := ∑' n : ℕ, (n : ℂ) ^ 2 * r ^ n
  have e1 : r / (1 - r) ^ 2 * (1 - r) ^ 2 = r := div_mul_cancel₀ _ (pow_ne_zero 2 hne)
  have e2 : (1 - r)⁻¹ * (1 - r) = 1 := inv_mul_cancel₀ hne
  rw [eq_div_iff (pow_ne_zero 3 hne)]
  linear_combination (1 - r) ^ 2 * hsplit + 2 * r * e1 + r * (1 - r) * e2

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in
/- English proof (translation)
Establish `h` using `EisensteinSeries.qExpansion_identity (k := 2) (by norm_num) ⟨z, hz⟩`. Establish `hq` using `UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩`. Simplify using `only [UpperHalfPlane.coe_mk] at h hq`. Simplify using `only [Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat] at h`. Rewrite using `[h, tsum_sq_mul_geometric_of_norm_lt_one hq]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma tsum_one_div_add_int_pow_three_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    ∑' m : ℤ, 1 / (z + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 *
      (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)
        * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z))
        / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * z)) ^ 3) := by
  have h := EisensteinSeries.qExpansion_identity (k := 2) (by norm_num) ⟨z, hz⟩
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one ⟨z, hz⟩
  simp only [UpperHalfPlane.coe_mk] at h hq
  simp only [Nat.reduceAdd, Nat.factorial_two, Nat.cast_ofNat] at h
  rw [h, tsum_sq_mul_geometric_of_norm_lt_one hq]
  ring

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
open Filter Topology in

/- English proof (translation)
Introduce `w hw hn`. Establish `hne : 1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) ≠ 0`. Introduce `h`. Establish `h1 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) = 1` using `by linear_combination -h`. Take `⟨n, hn'⟩` from `Complex.exp_eq_one_iff.mp h1`.

Apply `hn n` to reduce the goal to its premises. Establish `h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Take the linear combination `hn'`.

Establish `hE : ContinuousAt (fun x : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) w` using `by fun_prop`. Establish `hD2 : ContinuousAt (fun x : ℂ => (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) ^ 2) w` using `by fun_prop`. Establish `hD3 : ContinuousAt (fun x : ℂ => (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) ^ 3) w` using `by fun_prop`. Establish `hN3 : ContinuousAt (fun x : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x) * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x))) w` using `by fun_prop`. Prove the components needed by the constructor for the conclusion.

Conclude with `tsum_one_div_add_int_pow_of_real_of_continuousAt (k := 2) hw hn le_rfl (continuousAt_const.mul (hE.div hD2 (pow_ne_zero 2 hne))) tsum_one_div_add_int_sq_of_im_pos`. Conclude with `tsum_one_div_add_int_pow_of_real_of_continuousAt (k := 3) hw hn (by norm_num) (continuousAt_const.mul (hN3.div hD3 (pow_ne_zero 3 hne))) tsum_one_div_add_int_pow_three_of_im_pos`.
-/
theorem _root_.GlobalTheory.WpFam.RowReal.row_real : ∀ w : ℂ, w.im = 0 → (∀ n : ℤ, w ≠ n) → (∑' m : ℤ, 1 / (w + m) ^ 2 = (2 * (Real.pi : ℂ) * Complex.I) ^ 2 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 2)) ∧ ∑' m : ℤ, 1 / (w + m) ^ 3 = -(1 / 2) * (2 * (Real.pi : ℂ) * Complex.I) ^ 3 * (Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) / (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w)) ^ 3) := by
  intro w hw hn
  have hne : 1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) ≠ 0 := by
    intro h
    have h1 : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * w) = 1 := by linear_combination -h
    obtain ⟨n, hn'⟩ := Complex.exp_eq_one_iff.mp h1
    apply hn n
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ h2
    linear_combination hn'
  have hE : ContinuousAt (fun x : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) w := by
    fun_prop
  have hD2 : ContinuousAt
      (fun x : ℂ => (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) ^ 2) w := by
    fun_prop
  have hD3 : ContinuousAt
      (fun x : ℂ => (1 - Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)) ^ 3) w := by
    fun_prop
  have hN3 : ContinuousAt (fun x : ℂ => Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x)
      * (1 + Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * x))) w := by
    fun_prop
  constructor
  · exact tsum_one_div_add_int_pow_of_real_of_continuousAt (k := 2) hw hn le_rfl
      (continuousAt_const.mul (hE.div hD2 (pow_ne_zero 2 hne)))
      tsum_one_div_add_int_sq_of_im_pos
  · exact tsum_one_div_add_int_pow_of_real_of_continuousAt (k := 3) hw hn (by norm_num)
      (continuousAt_const.mul (hN3.div hD3 (pow_ne_zero 3 hne)))
      tsum_one_div_add_int_pow_three_of_im_pos

end GlobalTheory.WpFam.RowReal
