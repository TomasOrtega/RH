import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Legendre

noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter

namespace Formalism.L2.Th1.F

namespace EtaEis

/- English proof (translation)
Establish `hH : HasSum (fun N : ℕ => (a (N : ℤ) - a ((N : ℤ) + 1)) + (a (-((N : ℤ) + 1)) - a (-((N : ℤ) + 1) + 1))) (∑' m : ℤ, (a m - a (m + 1)))`. Conclude with `hs.hasSum.nat_add_neg_add_one`. Establish `hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((a (i : ℤ) - a ((i : ℤ) + 1)) + (a (-((i : ℤ) + 1)) - a (-((i : ℤ) + 1) + 1))) = a (-(N : ℤ)) - a (N : ℤ)`. Introduce `N`. Proceed by induction on `N with`.

Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[Finset.sum_range_succ, ih]`. Establish `e1 : -((k : ℤ) + 1) + 1 = -(k : ℤ)` using `by ring`. Rewrite using `[e1]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hlim` using `(h2.sub h1).congr (fun N => (hpart N).symm)`. Rewrite `hlim` using `[sub_zero]`. Conclude with `tendsto_nhds_unique hH.tendsto_sum_nat hlim`.
-/
lemma tsum_int_telescope (a : ℤ → ℂ) (hs : Summable fun m : ℤ => a m - a (m + 1))
    (h1 : Tendsto (fun N : ℕ => a (N : ℤ)) atTop (𝓝 0))
    (h2 : Tendsto (fun N : ℕ => a (-(N : ℤ))) atTop (𝓝 0)) :
    ∑' m : ℤ, (a m - a (m + 1)) = 0 := by
  have hH : HasSum (fun N : ℕ => (a (N : ℤ) - a ((N : ℤ) + 1))
      + (a (-((N : ℤ) + 1)) - a (-((N : ℤ) + 1) + 1))) (∑' m : ℤ, (a m - a (m + 1))) := by
    exact hs.hasSum.nat_add_neg_add_one
  have hpart : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((a (i : ℤ) - a ((i : ℤ) + 1))
      + (a (-((i : ℤ) + 1)) - a (-((i : ℤ) + 1) + 1))) = a (-(N : ℤ)) - a (N : ℤ) := by
    intro N
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have e1 : -((k : ℤ) + 1) + 1 = -(k : ℤ) := by ring
      rw [e1]
      push_cast
      ring
  have hlim := (h2.sub h1).congr (fun N => (hpart N).symm)
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hH.tendsto_sum_nat hlim

/- English proof (translation)
Establish `hinv : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹) atTop (𝓝 0)` using `by first`. Consider the case `exact RCLike.tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)`. Consider the case `(have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_nhds_zero_nat`. Simplify using `using h)`. Consider the case `(rw [Metric.tendsto_atTop]`.

Introduce `ε hε`. Take `⟨K, hK⟩` from `exists_nat_gt (1 / ε)`. Use `⟨K, fun n hn => ?_⟩` and prove the remaining obligations. Establish `hKpos : (0 : ℝ) < 1 / ε` using `by positivity`. Establish `hn' : (1 / ε : ℝ) < n` using `lt_of_lt_of_le hK (by exact_mod_cast hn)`.

Establish `hnpos : (0 : ℝ) < n` using `lt_trans hKpos hn'`. Establish `hnorm : ‖((n : ℂ))⁻¹‖ = ((n : ℝ))⁻¹` using `by simp`. Rewrite using `[dist_zero_right, hnorm, inv_eq_one_div, div_lt_iff₀ hnpos]`. Rewrite `hn'` using `[div_lt_iff₀ hε]`. Use the proof step `linarith)`.

Establish `h2 : Tendsto (fun N : ℕ => c * ((N : ℂ))⁻¹ + w) atTop (𝓝 (c * 0 + w))` using `(hinv.const_mul c).add_const w`. Rewrite `h2` using `[mul_zero, zero_add]`. Establish `h3 : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹ * (c * ((N : ℂ))⁻¹ + w)⁻¹) atTop (𝓝 (0 * w⁻¹))` using `hinv.mul (h2.inv₀ hw)`. Rewrite `h3` using `[zero_mul]`. Use `h3.congr' ?_` and prove the remaining obligations.

Use `filter_upwards [eventually_ge_atTop 1] with N hN`. Establish `hN0 : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (by omega)`. Rewrite using `[one_div, ← mul_inv]`. Use `congr 1`. Take the linear combination `c * mul_inv_cancel₀ hN0`.
-/
lemma tendsto_one_div_linear (c w : ℂ) (hw : w ≠ 0) :
    Tendsto (fun N : ℕ => 1 / (c + (N : ℂ) * w)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹) atTop (𝓝 0) := by
    first
    | exact RCLike.tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)
    | (have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_nhds_zero_nat
       simpa using h)
    | (rw [Metric.tendsto_atTop]
       intro ε hε
       obtain ⟨K, hK⟩ := exists_nat_gt (1 / ε)
       refine ⟨K, fun n hn => ?_⟩
       have hKpos : (0 : ℝ) < 1 / ε := by positivity
       have hn' : (1 / ε : ℝ) < n := lt_of_lt_of_le hK (by exact_mod_cast hn)
       have hnpos : (0 : ℝ) < n := lt_trans hKpos hn'
       have hnorm : ‖((n : ℂ))⁻¹‖ = ((n : ℝ))⁻¹ := by simp
       rw [dist_zero_right, hnorm, inv_eq_one_div, div_lt_iff₀ hnpos]
       rw [div_lt_iff₀ hε] at hn'
       linarith)
  have h2 : Tendsto (fun N : ℕ => c * ((N : ℂ))⁻¹ + w) atTop (𝓝 (c * 0 + w)) :=
    (hinv.const_mul c).add_const w
  rw [mul_zero, zero_add] at h2
  have h3 : Tendsto (fun N : ℕ => ((N : ℂ))⁻¹ * (c * ((N : ℂ))⁻¹ + w)⁻¹) atTop (𝓝 (0 * w⁻¹)) :=
    hinv.mul (h2.inv₀ hw)
  rw [zero_mul] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [one_div, ← mul_inv]
  congr 1
  linear_combination c * mul_inv_cancel₀ hN0

def tm (l x : ℂ) : ℂ := 1 / (x - l) + 1 / l + x / l ^ 2

/- English proof (translation)
Establish `hw' : 0 < ‖w‖` using `norm_pos_iff.mpr hw`. Take `⟨K, hK⟩` from `exists_nat_gt (2 * ‖c‖ / ‖w‖)`. Establish `hg : Summable fun N : ℕ => 4 / ‖w‖ ^ 2 * (1 / ((N + K : ℕ) : ℝ) ^ 2)`. Establish `h0 : Summable fun N : ℕ => 1 / (N : ℝ) ^ 2` using `Real.summable_one_div_nat_pow.mpr one_lt_two`. Conclude with `((summable_nat_add_iff K).mpr h0).mul_left _`.

Use `(summable_nat_add_iff K).mp (Summable.of_norm (hg.of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => ?_)))` and prove the remaining obligations. Use `show ‖1 / (((N + K : ℕ) : ℂ) * w + c) ^ 2‖ ≤ 4 / ‖w‖ ^ 2 * (1 / ((N + K : ℕ) : ℝ) ^ 2)`. Establish `hMK : K ≤ N + K` using `Nat.le_add_left K N`. Generalize the expression as in `N + K = M at hMK ⊢`. Establish `h1 : 2 * ‖c‖ / ‖w‖ < (M : ℝ)` using `lt_of_lt_of_le hK (by exact_mod_cast hMK)`.

Establish `h2 : 2 * ‖c‖ < (M : ℝ) * ‖w‖`. Conclude with `(div_lt_iff₀ hw').mp h1`. Establish `e : ‖(M : ℂ) * w‖ = (M : ℝ) * ‖w‖`. Simplify using the standard rewrite rules. Establish `h4 : ‖(M : ℂ) * w‖ ≤ ‖(M : ℂ) * w + c‖ + ‖c‖`.

Combine the equalities or inequalities in the displayed calculation. Rewrite `h4` using `[e]`. Establish `h3 : (M : ℝ) * ‖w‖ / 2 ≤ ‖(M : ℂ) * w + c‖` using `by linarith [norm_nonneg c]`. Establish `h5 : 0 < (M : ℝ) * ‖w‖ / 2` using `by linarith [norm_nonneg c]`. Establish `h6 : ((M : ℝ) * ‖w‖ / 2) ^ 2 ≤ ‖(M : ℂ) * w + c‖ ^ 2`.

Rewrite using `[sq, sq]`. Conclude with `mul_le_mul h3 h3 h5.le (norm_nonneg _)`. Rewrite using `[norm_div, norm_one, norm_pow]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem summable_inv_sq_nat_mul_add (c w : ℂ) (hw : w ≠ 0) :
    Summable fun N : ℕ => 1 / ((N : ℂ) * w + c) ^ 2 := by
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  obtain ⟨K, hK⟩ := exists_nat_gt (2 * ‖c‖ / ‖w‖)
  have hg : Summable fun N : ℕ => 4 / ‖w‖ ^ 2 * (1 / ((N + K : ℕ) : ℝ) ^ 2) := by
    have h0 : Summable fun N : ℕ => 1 / (N : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
    exact ((summable_nat_add_iff K).mpr h0).mul_left _
  refine (summable_nat_add_iff K).mp
    (Summable.of_norm (hg.of_nonneg_of_le (fun _ => norm_nonneg _) (fun N => ?_)))
  show ‖1 / (((N + K : ℕ) : ℂ) * w + c) ^ 2‖ ≤ 4 / ‖w‖ ^ 2 * (1 / ((N + K : ℕ) : ℝ) ^ 2)
  have hMK : K ≤ N + K := Nat.le_add_left K N
  generalize N + K = M at hMK ⊢
  have h1 : 2 * ‖c‖ / ‖w‖ < (M : ℝ) := lt_of_lt_of_le hK (by exact_mod_cast hMK)
  have h2 : 2 * ‖c‖ < (M : ℝ) * ‖w‖ := by
    exact (div_lt_iff₀ hw').mp h1
  have e : ‖(M : ℂ) * w‖ = (M : ℝ) * ‖w‖ := by
    simp
  have h4 : ‖(M : ℂ) * w‖ ≤ ‖(M : ℂ) * w + c‖ + ‖c‖ := by
    calc ‖(M : ℂ) * w‖ = ‖((M : ℂ) * w + c) - c‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖(M : ℂ) * w + c‖ + ‖c‖ := norm_sub_le _ _
  rw [e] at h4
  have h3 : (M : ℝ) * ‖w‖ / 2 ≤ ‖(M : ℂ) * w + c‖ := by linarith [norm_nonneg c]
  have h5 : 0 < (M : ℝ) * ‖w‖ / 2 := by linarith [norm_nonneg c]
  have h6 : ((M : ℝ) * ‖w‖ / 2) ^ 2 ≤ ‖(M : ℂ) * w + c‖ ^ 2 := by
    rw [sq, sq]; exact mul_le_mul h3 h3 h5.le (norm_nonneg _)
  rw [norm_div, norm_one, norm_pow]
  calc 1 / ‖(M : ℂ) * w + c‖ ^ 2 ≤ 1 / ((M : ℝ) * ‖w‖ / 2) ^ 2 :=
        one_div_le_one_div_of_le (pow_pos h5 2) h6
    _ = 4 / ‖w‖ ^ 2 * (1 / (M : ℝ) ^ 2) := by ring

/- English proof (translation)
Establish `hp : Summable fun N : ℕ => 1 / (((N : ℤ) : ℂ) * u + (n : ℂ) * v) ^ 2`. Use `(summable_inv_sq_nat_mul_add ((n : ℂ) * v) u hu).congr (fun N => ?_)` and prove the remaining obligations. Simplify using `only [Int.cast_natCast]`. Establish `hm : Summable fun N : ℕ => 1 / (((-(N : ℤ) : ℤ) : ℂ) * u + (n : ℂ) * v) ^ 2`. Use `(summable_inv_sq_nat_mul_add ((n : ℂ) * v) (-u) (neg_ne_zero.mpr hu)).congr (fun N => ?_)` and prove the remaining obligations.

Rewrite using `[Int.cast_neg, Int.cast_natCast, neg_mul, mul_neg]`. Conclude with `summable_int_iff_summable_nat_and_neg.mpr ⟨hp, hm⟩`.
-/
lemma summable_inv_sq (u v : ℂ) (hu : u ≠ 0) (n : ℤ) :
    Summable fun m : ℤ => 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 := by
  have hp : Summable fun N : ℕ => 1 / (((N : ℤ) : ℂ) * u + (n : ℂ) * v) ^ 2 := by
    refine (summable_inv_sq_nat_mul_add ((n : ℂ) * v) u hu).congr (fun N => ?_)
    simp only [Int.cast_natCast]
  have hm : Summable fun N : ℕ => 1 / (((-(N : ℤ) : ℤ) : ℂ) * u + (n : ℂ) * v) ^ 2 := by
    refine (summable_inv_sq_nat_mul_add ((n : ℂ) * v) (-u) (neg_ne_zero.mpr hu)).congr (fun N => ?_)
    rw [Int.cast_neg, Int.cast_natCast, neg_mul, mul_neg]
  exact summable_int_iff_summable_nat_and_neg.mpr ⟨hp, hm⟩

/- English proof (translation)
Unfold `tm`. Rewrite using `[show -(u / 2) - l = u / 2 - (l + u) by ring]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem tm_half_sub_tm_neg_half (u l : ℂ) :
    tm l (u / 2) - tm l (-(u / 2))
      = 1 / (u / 2 - l) - 1 / (u / 2 - (l + u)) + u * (1 / l ^ 2) := by
  unfold tm
  rw [show -(u / 2) - l = u / 2 - (l + u) by ring]
  ring

/- English proof (translation)
Establish `hq` using `summable_inv_sq u v hu n`. Establish `hsplit : ∀ m : ℤ, tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2) - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2)) = (1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v)) - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v))) + u * (1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2)`. Introduce `m`. Rewrite using `[tm_half_sub_tm_neg_half, Int.cast_add, Int.cast_one, show ((m : ℂ) + 1) * u + (n : ℂ) * v = (m : ℂ) * u + (n : ℂ) * v + u by ring]`. Establish `htel : Summable fun m : ℤ => 1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v)) - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v))`.

Use `(hfib.sub (hq.mul_left u)).congr (fun m => ?_)` and prove the remaining obligations. Rewrite using `[hsplit m]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlim1 : Tendsto (fun N : ℕ => 1 / (u / 2 - (((N : ℤ) : ℂ) * u + (n : ℂ) * v))) atTop (𝓝 0)`. Use `(tendsto_one_div_linear (u / 2 - (n : ℂ) * v) (-u) (neg_ne_zero.mpr hu)).congr (fun N => ?_)` and prove the remaining obligations.

Use `push_cast`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `hlim2 : Tendsto (fun N : ℕ => 1 / (u / 2 - (((-(N : ℤ) : ℤ) : ℂ) * u + (n : ℂ) * v))) atTop (𝓝 0)`. Use `(tendsto_one_div_linear (u / 2 - (n : ℂ) * v) u hu).congr (fun N => ?_)` and prove the remaining obligations.

Use `push_cast`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `ht : ∑' m : ℤ, (1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v)) - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v))) = 0` using `tsum_int_telescope (fun k : ℤ => 1 / (u / 2 - ((k : ℂ) * u + (n : ℂ) * v))) htel hlim1 hlim2`. Establish `hadd : ∑' m : ℤ, ((1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v)) - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v))) + u * (1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2)) = ∑' m : ℤ, (1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v)) - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v))) + ∑' m : …`.

Conclude with `htel.tsum_add (hq.mul_left u)`. Rewrite using `[tsum_congr hsplit, hadd, ht, zero_add, tsum_mul_left]`.
-/
private theorem tsum_zeta_half_diff_eq_mul_tsum_inv_sq (u v : ℂ) (hu : u ≠ 0) (n : ℤ)
    (hfib : Summable fun m : ℤ => tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
      - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2))) :
    ∑' m : ℤ, (tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
      - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2)))
      = u * ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 := by
  have hq := summable_inv_sq u v hu n
  have hsplit : ∀ m : ℤ, tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
      - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2))
      = (1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v))
          - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v)))
        + u * (1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) := by
    intro m
    rw [tm_half_sub_tm_neg_half, Int.cast_add, Int.cast_one,
      show ((m : ℂ) + 1) * u + (n : ℂ) * v = (m : ℂ) * u + (n : ℂ) * v + u by ring]
  have htel : Summable fun m : ℤ => 1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v))
      - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v)) := by
    refine (hfib.sub (hq.mul_left u)).congr (fun m => ?_)
    rw [hsplit m]; ring
  have hlim1 : Tendsto (fun N : ℕ => 1 / (u / 2 - (((N : ℤ) : ℂ) * u + (n : ℂ) * v)))
      atTop (𝓝 0) := by
    refine (tendsto_one_div_linear (u / 2 - (n : ℂ) * v) (-u) (neg_ne_zero.mpr hu)).congr
      (fun N => ?_)
    push_cast; congr 1; ring
  have hlim2 : Tendsto (fun N : ℕ => 1 / (u / 2 - (((-(N : ℤ) : ℤ) : ℂ) * u + (n : ℂ) * v)))
      atTop (𝓝 0) := by
    refine (tendsto_one_div_linear (u / 2 - (n : ℂ) * v) u hu).congr (fun N => ?_)
    push_cast; congr 1; ring
  have ht : ∑' m : ℤ, (1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v))
      - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v))) = 0 :=
    tsum_int_telescope (fun k : ℤ => 1 / (u / 2 - ((k : ℂ) * u + (n : ℂ) * v))) htel hlim1 hlim2
  have hadd : ∑' m : ℤ, ((1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v))
          - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v)))
        + u * (1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2))
      = ∑' m : ℤ, (1 / (u / 2 - ((m : ℂ) * u + (n : ℂ) * v))
          - 1 / (u / 2 - (((m + 1 : ℤ) : ℂ) * u + (n : ℂ) * v)))
        + ∑' m : ℤ, u * (1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2) := by
    exact htel.tsum_add (hq.mul_left u)
  rw [tsum_congr hsplit, hadd, ht, zero_add, tsum_mul_left]

/- English proof (translation)
Establish `hsum : Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2) - tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2))` using `(hS _).sub (hS _)`. Establish `hfib : ∀ n : ℤ, Summable fun m : ℤ => tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2) - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2))`. Introduce `n`. Conclude with `hsum.prod_factor n`. Establish `h1 : (∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2)) - ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2)) = ∑' p : ℤ × ℤ, (tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2) - tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2)))`.

Conclude with `((hS _).tsum_sub (hS _)).symm`. Establish `h2 : ∑' p : ℤ × ℤ, (tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2) - tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2))) = ∑' n : ℤ, ∑' m : ℤ, (tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2) - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2)))`. Conclude with `hsum.tsum_prod' hfib`. Rewrite using `[h1, h2, ← tsum_mul_left]`. Conclude with `tsum_congr (fun n => tsum_zeta_half_diff_eq_mul_tsum_inv_sq u v hu n (hfib n))`.
-/
lemma core (u v : ℂ) (hu : u ≠ 0)
    (hS : ∀ x : ℂ, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) x) :
    (∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2))
      - ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2))
      = u * ∑' n : ℤ, ∑' m : ℤ, 1 / ((m : ℂ) * u + (n : ℂ) * v) ^ 2 := by
  have hsum : Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2)
      - tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2)) := (hS _).sub (hS _)
  have hfib : ∀ n : ℤ, Summable fun m : ℤ => tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
      - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2)) := by
    intro n
    exact hsum.prod_factor n
  have h1 : (∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2))
      - ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2))
      = ∑' p : ℤ × ℤ, (tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2)
          - tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2))) := by
    exact ((hS _).tsum_sub (hS _)).symm
  have h2 : ∑' p : ℤ × ℤ, (tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (u / 2)
          - tm ((p.2 : ℂ) * u + (p.1 : ℂ) * v) (-(u / 2)))
      = ∑' n : ℤ, ∑' m : ℤ, (tm ((m : ℂ) * u + (n : ℂ) * v) (u / 2)
          - tm ((m : ℂ) * u + (n : ℂ) * v) (-(u / 2))) := by
    exact hsum.tsum_prod' hfib
  rw [h1, h2, ← tsum_mul_left]
  exact tsum_congr (fun n => tsum_zeta_half_diff_eq_mul_tsum_inv_sq u v hu n (hfib n))

end EtaEis

open EtaEis in
/- English proof (translation)
Introduce `L`. Establish `hu1 : L.ω₁ ≠ 0`. Introduce `h; exact L.ω₁_div_two_notMem_lattice (by rw [h]; simp)`. Establish `hu2 : L.ω₂ ≠ 0`. Introduce `h; exact L.ω₂_div_two_notMem_lattice (by rw [h]; simp)`.

Establish `hS2 : ∀ x : ℂ, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * L.ω₂ + (p.1 : ℂ) * L.ω₁) x`. Introduce `x`. Use `((L.latticeEquivProd.symm.toEquiv.summable_iff).mpr (hs L x)).congr fun p => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, tm, add_comm]`. Establish `hZ2 : ∀ x : ℂ, wZeta L x = ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * L.ω₂ + (p.1 : ℂ) * L.ω₁) x`.

Introduce `x`. Rewrite using `[wZeta, ← L.latticeEquivProd.symm.toEquiv.tsum_eq]`. Use `tsum_congr fun p => ?_` and prove the remaining obligations. Simplify using `only [LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, tm, add_comm]`. Establish `hS1 : ∀ x : ℂ, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * L.ω₁ + (p.1 : ℂ) * L.ω₂) x`.

Introduce `x`. Use `(((Equiv.prodComm ℤ ℤ).summable_iff).mpr (hS2 x)).congr fun p => ?_` and prove the remaining obligations. Simplify using `only [Function.comp, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm]`. Establish `hZ1 : ∀ x : ℂ, wZeta L x = ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * L.ω₁ + (p.1 : ℂ) * L.ω₂) x`. Introduce `x`.

Rewrite using `[hZ2, ← (Equiv.prodComm ℤ ℤ).tsum_eq]`. Use `tsum_congr fun p => ?_` and prove the remaining obligations. Simplify using `only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm]`. Establish `hE1 : wEta L L.ω₁ = 2 * wZeta L (L.ω₁ / 2)`. Use `L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 0` as an intermediate fact.

Simplify `this` using `[wEta]`. Establish `hE2 : wEta L L.ω₂ = 2 * wZeta L (L.ω₂ / 2)`. Use `L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1` as an intermediate fact. Simplify `this` using `[wEta]`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[hE1, ← core L.ω₁ L.ω₂ hu1 hS1, ← hZ1, ← hZ1, ho]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `core L.ω₂ L.ω₁ hu2 hS2`. Rewrite `h` using `[← hZ2, ← hZ2, ho]`. Rewrite using `[hE2]`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use `tsum_congr fun m => tsum_congr fun n => ?_` and prove the remaining obligations. Rewrite using `[add_comm]`.
-/
theorem etaEisenstein_of (hs : ZetaSummable) (ho : ZetaOdd) : EtaEisenstein := by
  intro L
  have hu1 : L.ω₁ ≠ 0 := by
    intro h; exact L.ω₁_div_two_notMem_lattice (by rw [h]; simp)
  have hu2 : L.ω₂ ≠ 0 := by
    intro h; exact L.ω₂_div_two_notMem_lattice (by rw [h]; simp)

  have hS2 : ∀ x : ℂ, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * L.ω₂ + (p.1 : ℂ) * L.ω₁) x := by
    intro x
    refine ((L.latticeEquivProd.symm.toEquiv.summable_iff).mpr (hs L x)).congr fun p => ?_
    simp only [Function.comp, LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, tm, add_comm]
  have hZ2 : ∀ x : ℂ, wZeta L x = ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * L.ω₂ + (p.1 : ℂ) * L.ω₁) x := by
    intro x
    rw [wZeta, ← L.latticeEquivProd.symm.toEquiv.tsum_eq]
    refine tsum_congr fun p => ?_
    simp only [LinearEquiv.coe_toEquiv, L.latticeEquiv_symm_apply, tm, add_comm]
  have hS1 : ∀ x : ℂ, Summable fun p : ℤ × ℤ => tm ((p.2 : ℂ) * L.ω₁ + (p.1 : ℂ) * L.ω₂) x := by
    intro x
    refine (((Equiv.prodComm ℤ ℤ).summable_iff).mpr (hS2 x)).congr fun p => ?_
    simp only [Function.comp, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm]
  have hZ1 : ∀ x : ℂ, wZeta L x = ∑' p : ℤ × ℤ, tm ((p.2 : ℂ) * L.ω₁ + (p.1 : ℂ) * L.ω₂) x := by
    intro x
    rw [hZ2, ← (Equiv.prodComm ℤ ℤ).tsum_eq]
    refine tsum_congr fun p => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, add_comm]
  have hE1 : wEta L L.ω₁ = 2 * wZeta L (L.ω₁ / 2) := by
    have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 0
    simpa [wEta] using this
  have hE2 : wEta L L.ω₂ = 2 * wZeta L (L.ω₂ / 2) := by
    have := L.basis.constr_basis ℝ ![2 * wZeta L (L.ω₁ / 2), 2 * wZeta L (L.ω₂ / 2)] 1
    simpa [wEta] using this
  constructor
  · rw [hE1, ← core L.ω₁ L.ω₂ hu1 hS1, ← hZ1, ← hZ1, ho]; ring
  · have h := core L.ω₂ L.ω₁ hu2 hS2
    rw [← hZ2, ← hZ2, ho] at h
    rw [hE2]
    calc 2 * wZeta L (L.ω₂ / 2) = wZeta L (L.ω₂ / 2) - -wZeta L (L.ω₂ / 2) := by ring
      _ = _ := h
      _ = _ := by
        congr 1
        refine tsum_congr fun m => tsum_congr fun n => ?_
        rw [add_comm]

end Formalism.L2.Th1.F
