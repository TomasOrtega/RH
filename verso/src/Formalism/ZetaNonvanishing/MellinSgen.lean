import Formalism.DefsOC
import Formalism.ZetaNonvanishing.MellinSAux

open Complex MeasureTheory Set Filter Topology ArithmeticFunction

noncomputable section

namespace Formalism

section
variable (a : ℕ → ℝ)

/- English proof (authored)
For each fixed upper index the weighted partial sum is a finite sum of measurable functions of x. The natural numbers are countable, so the joint function of x and the upper index is measurable. Substituting the measurable natural floor of x for the upper index gives the claim.
-/
lemma Sa_measurable : Measurable (Sa a) := by
  have hk : ∀ k : ℕ, Measurable fun x : ℝ => ∑ n ∈ Finset.Icc 1 k, a n * (x / n - 1) :=
    fun k => Finset.measurable_sum _ fun n _ => by fun_prop
  unfold Sa
  first
    | (have hg : Measurable (fun p : ℝ × ℕ => ∑ n ∈ Finset.Icc 1 p.2, a n * (p.1 / n - 1)) := by
        first
          | exact measurable_from_prod_countable_right hk
          | exact measurable_from_prod_countable_left hk
          | exact measurable_from_prod_countable hk
       exact hg.comp (measurable_id.prodMk Nat.measurable_floor))
    | (have hg : Measurable (fun p : ℕ × ℝ => ∑ n ∈ Finset.Icc 1 p.1, a n * (p.2 / n - 1)) := by
        first
          | exact measurable_from_prod_countable_left hk
          | exact measurable_from_prod_countable_right hk
       exact hg.comp (Nat.measurable_floor.prodMk measurable_id))

/- English proof (authored)
An index outside the summation interval is either zero or above the natural floor of x. The coefficient at zero vanishes. In the second case n > x and n is positive, so x/n − 1 is nonpositive and the kernel vanishes.
-/
lemma a_mxS_eq_zero (ha0 : a 0 = 0) (x : ℝ) (n : ℕ) (hn : n ∉ Finset.Icc 1 ⌊x⌋₊) :
    a n * mxS n x = 0 := by
  unfold mxS
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
  rcases hn with hn | hn
  · have h0 : n = 0 := by omega
    subst h0
    simp [ha0]
  · have hx : x < n := Nat.lt_of_floor_lt hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hle : x / n - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one hn0]
      exact hx.le
    rw [max_eq_right hle, mul_zero]

/- English proof (authored)
Outside the finite interval from 1 to the natural floor of x, all terms vanish. Inside that interval n is positive and n ≤ x, so the positive-part kernel equals x/n − 1. The infinite sum therefore reduces to the defining finite sum.
-/
lemma Sa_eq_tsum (ha0 : a 0 = 0) (x : ℝ) : Sa a x = ∑' n, a n * mxS n x := by
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => a_mxS_eq_zero a ha0 x n hn)]
  unfold Sa
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hx : (n : ℝ) ≤ x := by
    have hx0 : 0 ≤ x := by
      by_contra hneg
      push_neg at hneg
      rw [Nat.floor_eq_zero.mpr (by linarith)] at hn
      omega
    exact (Nat.le_floor_iff hx0).mp hn.2
  have hnn : 0 ≤ x / n - 1 := by
    rw [sub_nonneg, le_div_iff₀ hn0]
    linarith
  unfold mxS
  rw [max_eq_left hnn]

/- English proof (authored)
At each fixed x the terms vanish outside the finite interval from 1 to the natural floor of x. A finitely supported series is summable.
-/
lemma summable_a_mxS (ha0 : a 0 = 0) (x : ℝ) : Summable (fun n => a n * mxS n x) :=
  summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => a_mxS_eq_zero a ha0 x n hn)

/- English proof (authored)
Use the finite-support expression of the sum and apply the triangle inequality term by term. The kernel is nonnegative, so each absolute value acts only on the coefficient. Extending the resulting finite sum to all natural indices preserves its value because the other terms vanish.
-/
lemma abs_Sa_le (ha0 : a 0 = 0) (x : ℝ) : |Sa a x| ≤ ∑' n, |a n| * mxS n x := by
  have hm : ∀ n, 0 ≤ mxS n x := fun n => by
    unfold mxS
    exact le_max_right _ _
  rw [Sa_eq_tsum a ha0 x, tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => a_mxS_eq_zero a ha0 x n hn),
    tsum_eq_sum (s := Finset.Icc 1 ⌊x⌋₊) (fun n hn => by
      have h := a_mxS_eq_zero a ha0 x n hn
      rcases mul_eq_zero.mp h with h | h <;> simp [h])]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
  rw [abs_mul, abs_of_nonneg (hm n)]

/- English proof (authored)
For n > 0 the weighted absolute coefficient is bounded by the absolute value of K times the corresponding nonnegative von Mangoldt term divided by n to the power σ. The latter series converges for σ > 1. The zero index contributes zero, so comparison proves summability.
-/
lemma summable_abs_a (K : ℝ) (hK : ∀ n : ℕ, |a n| ≤ K * vonMangoldt n) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => |a n| * (n : ℝ) ^ (-σ)) := by
  have hs : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (fun n => ?_) (hs.norm.mul_left |K|)
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp [Real.zero_rpow (by linarith : -σ ≠ 0)]
  · have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [LSeries.norm_term_eq, if_neg hn.ne']
    simp only [Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg hΛ]
    rw [div_eq_mul_inv, ← Real.rpow_neg hnpos.le]
    have hK' : |a n| ≤ |K| * ArithmeticFunction.vonMangoldt n :=
      (hK n).trans (mul_le_mul_of_nonneg_right (le_abs_self K) hΛ)
    calc |a n| * (n : ℝ) ^ (-σ) ≤ |K| * ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hK' (Real.rpow_nonneg hnpos.le _)
      _ = |K| * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-σ)) := by ring

end

/- English proof (authored)
The coefficient bound forces the coefficient at zero to vanish, and the finite-sum construction is measurable. For real σ > 1, the weighted absolute sum is bounded by the sum obtained by assigning each kernel the absolute value of its coefficient. The real kernel transform evaluates each term's integral, and the resulting sequence is summable by comparison with the von Mangoldt series. Tonelli's theorem makes the absolute majorant integrable. For complex s with real part above 1, the norm of each complex summand is precisely the corresponding term of that majorant at σ equal to the real part of s. Thus the sum and integral may be interchanged. Using the complex transform term by term produces the Dirichlet series divided by s(s − 1).
-/
theorem mellinSgen : MellinSgen := by
  intro a K hK
  have ha0 : a 0 = 0 := by
    have h := hK 0
    rw [ArithmeticFunction.map_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  refine ⟨Sa_measurable a, fun σ hσ => ?_, fun s hs => ?_⟩
  · have key := integrable_tsum_of_nonneg (μ := volume.restrict (Ioi (1 : ℝ)))
      (φ := fun n x => |a n| * (mxS n x * x ^ (-σ - 1))) (fun n => ?_) (fun n => ?_)
      (fun x => ?_) ?_
    · have hmeas : Measurable (fun x : ℝ => |Sa a x| * x ^ (-σ - 1)) := by
        have := Sa_measurable a
        fun_prop
      refine key.mono' hmeas.aestronglyMeasurable ?_
      refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
      have hxp : 0 ≤ x ^ (-σ - 1) := Real.rpow_nonneg hx0.le _
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) hxp)]
      calc |Sa a x| * x ^ (-σ - 1) ≤ (∑' n, |a n| * mxS n x) * x ^ (-σ - 1) :=
            mul_le_mul_of_nonneg_right (abs_Sa_le a ha0 x) hxp
        _ = ∑' n, |a n| * (mxS n x * x ^ (-σ - 1)) := by
            rw [← tsum_mul_right]; congr 1; funext n; ring
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [ha0]
      · exact ((mxS_mellin_real hn hσ).1).const_mul _
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun x hx => ?_
      exact mul_nonneg (abs_nonneg _) (mul_nonneg (mxS_nonneg n x)
        (Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hx)) _))
    · have ha0' : |a 0| = 0 := by simp [ha0]
      simpa only [mul_assoc] using
        (summable_a_mxS (fun n => |a n|) ha0' x).mul_right (x ^ (-σ - 1))
    · have : (fun n => ∫ x in Ioi (1 : ℝ), |a n| * (mxS n x * x ^ (-σ - 1))) =
          fun n : ℕ => |a n| * (n : ℝ) ^ (-σ) / (σ * (σ - 1)) := by
        funext n
        rw [integral_const_mul]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [ha0]
        · rw [(mxS_mellin_real hn hσ).2]; ring
      rw [this]; exact (summable_abs_a a K hK hσ).div_const _
  · set F : ℕ → ℝ → ℂ := fun n x => (a n : ℂ) * ((mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) with hFdef
    have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi (1 : ℝ))) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [F, ha0]
      · exact ((mxS_mellin hn hs).1).const_mul _
    have hnorm : ∀ n, ∫ x in Ioi (1 : ℝ), ‖F n x‖ =
        |a n| * (n : ℝ) ^ (-s.re) / (s.re * (s.re - 1)) := by
      intro n
      rw [setIntegral_congr_fun measurableSet_Ioi
        (g := fun x => |a n| * (mxS n x * x ^ (-s.re - 1))) (fun x hx => ?_)]
      · rw [integral_const_mul]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [ha0]
        · rw [(mxS_mellin_real hn hs).2]; ring
      · have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
        simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (mxS_nonneg n x), norm_cpow_eq_rpow_re_of_pos hx0]
        congr 3
    have hsum : Summable (fun n => ∫ x in Ioi (1 : ℝ), ‖F n x‖) := by
      simp_rw [hnorm]; exact (summable_abs_a a K hK hs).div_const _
    have hpt : ∀ x ∈ Ioi (1 : ℝ), (Sa a x : ℂ) * (x : ℂ) ^ (-s - 1) = ∑' n, F n x := by
      intro x hx
      rw [Sa_eq_tsum a ha0, ofReal_tsum, ← tsum_mul_right]
      congr 1; funext n; simp only [F]; push_cast; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt,
      ← integral_tsum_of_summable_integral_norm hint hsum, LSeries, ← tsum_div_const]
    congr 1; funext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F, ha0]
    · simp only [F]
      rw [integral_const_mul, (mxS_mellin hn hs).2, LSeries.term_of_ne_zero (by omega), cpow_neg]
      ring

end Formalism
