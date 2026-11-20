import Mathlib
import Formalism.DirichletDensity.Statement

open Filter Topology Set

noncomputable section

namespace Formalism.HF.P

/- English proof (authored)
For positive integer n, log n is nonnegative and the denominator is positive. At zero the numerator is zero under the real-logarithm convention used here.
-/
lemma log_div_rpow_nonneg (n : ℕ) (x : ℝ) : 0 ≤ Real.log n / (n : ℝ) ^ x :=
  div_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) x)

/- English proof (authored)
Choose ε = (y − 1)/2 > 0. For positive n, the inequality log n ≤ nᵋ/ε bounds the summand by 1/(ε n raised to y − ε). The exponent y − ε is greater than one, so the comparison series converges. The zero term vanishes.
-/
lemma summable_log_div_rpow {y : ℝ} (hy : 1 < y) :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ y) := by
  set ε := (y - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hs : Summable (fun n : ℕ => (1 / ε) * ((n : ℝ) ^ (y - ε))⁻¹) :=
    (Real.summable_nat_rpow_inv.2 (by rw [hε]; linarith)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => log_div_rpow_nonneg n y) (fun n => ?_) hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, Real.log_zero, zero_div]
    exact mul_nonneg (div_nonneg zero_le_one hε0.le) (inv_nonneg.2 (Real.rpow_nonneg le_rfl _))
  · have hn' : (0:ℝ) < n := Nat.cast_pos.2 hn
    have h1 := Real.log_le_rpow_div hn'.le hε0
    have hpos : 0 < (n:ℝ) ^ y := Real.rpow_pos_of_pos hn' y
    have hposε : 0 < (n:ℝ) ^ ε := Real.rpow_pos_of_pos hn' ε
    calc Real.log n / (n:ℝ) ^ y ≤ ((n:ℝ) ^ ε / ε) / (n:ℝ) ^ y := by gcongr
      _ = (1 / ε) * ((n:ℝ) ^ (y - ε))⁻¹ := by
        rw [Real.rpow_sub hn', inv_div]
        field_simp

/- English proof (authored)
If n is a prime belonging to S, then n is positive, and differentiating exp(−x log n) gives −log n times that function. For every other n the summand is identically zero, so its derivative is zero.
-/
lemma hasDerivAt_term (S : Set ℕ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => 1 / (m : ℝ) ^ x) n)
      (-{p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) x := by
  by_cases h : n ∈ {p : ℕ | p.Prime ∧ p ∈ S}
  · simp only [Set.indicator_of_mem h]
    have hn : (0:ℝ) < n := Nat.cast_pos.2 h.1.pos
    have h1 := (Real.hasStrictDerivAt_const_rpow hn x).hasDerivAt
    have h2 := h1.inv (Real.rpow_pos_of_pos hn x).ne'
    have hfun : (fun x : ℝ => 1 / (n:ℝ) ^ x) = fun x => ((n:ℝ) ^ x)⁻¹ := by
      funext z; exact one_div _
    have h3 : HasDerivAt (fun x : ℝ => ((n:ℝ) ^ x)⁻¹) (-((n:ℝ) ^ x * Real.log n) / ((n:ℝ) ^ x) ^ 2) x := h2
    rw [hfun]
    refine h3.congr_deriv ?_
    have : 0 < (n:ℝ) ^ x := Real.rpow_pos_of_pos hn x
    rw [neg_div, pow_two, mul_div_mul_left _ _ this.ne']
  · simp only [Set.indicator_of_notMem h, neg_zero]
    exact hasDerivAt_const x 0

/- English proof (authored)
Each summand is nonnegative and is at most the corresponding term of the convergent p-series with exponent x > 1. Comparison gives summability.
-/
lemma summable_F (S : Set ℕ) {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => 1 / (m : ℝ) ^ x) n) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (Real.summable_nat_rpow_inv.2 hx)
  · exact Set.indicator_nonneg (fun m _ => by positivity) n
  · calc _ ≤ 1 / (n:ℝ) ^ x := Set.indicator_le_self' (fun m _ => by positivity) n
      _ = _ := one_div _

/- English proof (authored)
Choose y strictly between one and x. For arguments above y, each summand has the termwise derivative given by the prime indicator times −log n divided by the corresponding power of n. Its absolute value is bounded by log n divided by nʸ for positive n, and the derivative at index zero vanishes. These bounds are summable. The original series converges at x, so the uniform derivative bound justifies termwise differentiation on the interval above y.
-/
lemma hasDerivAt_F (S : Set ℕ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x : ℝ => ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator
        (fun m : ℕ => 1 / (m : ℝ) ^ x) n)
      (-∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n)
      x := by
  set y := (1 + x) / 2 with hy
  have hy1 : 1 < y := by rw [hy]; linarith
  have hyx : y < x := by rw [hy]; linarith
  rw [← tsum_neg]
  refine hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => Real.log n / (n : ℝ) ^ y)
    (g := fun n z => {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => 1 / (m : ℝ) ^ z) n)
    (g' := fun n z => -{p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ z) n)
    (summable_log_div_rpow hy1) isOpen_Ioi isPreconnected_Ioi
    (fun n z _ => hasDerivAt_term S n z) (fun n z hz => ?_) (mem_Ioi.2 hyx) ?_ (mem_Ioi.2 hyx)
  · have hz' : y < z := mem_Ioi.1 hz
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (Set.indicator_nonneg (fun m _ => log_div_rpow_nonneg m z) n)]
    refine (Set.indicator_le_self' (fun m _ => log_div_rpow_nonneg m z) n).trans ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn1 : (1:ℝ) ≤ n := Nat.one_le_cast.2 hn
      have hpos : 0 < (n:ℝ) ^ y := Real.rpow_pos_of_pos (by linarith) y
      exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg n) hpos
        (Real.rpow_le_rpow_of_exponent_le hn1 hz'.le)
  · exact summable_F S (by linarith)

/- English proof (authored)
As x tends to one from above, x − 1 tends to zero through positive values. Its logarithm tends to negative infinity, and negating it gives the logarithm of the reciprocal, which tends to positive infinity.
-/
lemma tendsto_log_inv_sub_one :
    Tendsto (fun x : ℝ => Real.log (1 / (x - 1))) (𝓝[>] 1) atTop := by
  have h1 : Tendsto (fun x : ℝ => x - 1) (𝓝[>] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun x : ℝ => x - 1) (𝓝 1) (𝓝 (1 - 1)) :=
        (continuous_sub_right (1:ℝ)).tendsto 1
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall (fun x hx => mem_Ioi.2 (sub_pos.2 hx))
  have h2 := tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h1)
  refine h2.congr (fun x => ?_)
  simp only [Function.comp_apply, one_div, Real.log_inv]

/- English proof (authored)
Let F(x) be the sum of p raised to −x over primes in S and let G(x) be the corresponding sum weighted by log p. Then F′ = −G. For every ε > 0 and x sufficiently close to one from above, the logarithmic density hypothesis bounds G(x) between (δ − ε)/(x − 1) and (δ + ε)/(x − 1). The derivative signs imply that F(x) plus (δ + ε) log(x − 1) is nondecreasing and F(x) plus (δ − ε) log(x − 1) is nonincreasing on a short interval. Comparing each with its value at a fixed right endpoint bounds F(x) between (δ − ε) log(1/(x − 1)) and (δ + ε) log(1/(x − 1)), up to additive constants. Divide by the logarithm, which tends to infinity, and let ε decrease to zero.
-/
theorem dirichlet_density_of_log_density (S : Set ℕ) (δ : ℝ) (h : LogDensity S δ) : DirDensity S δ := by
  unfold LogDensity at h
  unfold DirDensity
  set f : ℝ → ℝ := fun x => ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator
    (fun m : ℕ => 1 / (m : ℝ) ^ x) n with hf
  set g : ℝ → ℝ := fun x => ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator
    (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n with hg
  set L : ℝ → ℝ := fun x => Real.log (1 / (x - 1)) with hLdef
  have hder : ∀ x, 1 < x → HasDerivAt f (-g x) x := fun x hx => hasDerivAt_F S hx
  have hlogder : ∀ t : ℝ, 1 < t → HasDerivAt (fun t : ℝ => Real.log (t - 1)) (1 / (t - 1)) t :=
    fun t ht => ((hasDerivAt_id' t).sub_const 1).log (sub_pos.2 ht).ne'
  have hL : Tendsto L (𝓝[>] 1) atTop := tendsto_log_inv_sub_one
  have hLeq : ∀ x, L x = -Real.log (x - 1) := fun x => by
    simp only [hLdef, one_div, Real.log_inv]
  rw [Metric.tendsto_nhds]
  intro ε hε
  set e := ε / 4 with he
  have he0 : 0 < e := by rw [he]; linarith
  have hev := (Metric.tendsto_nhds.1 h) e he0
  rw [Filter.eventually_iff, mem_nhdsGT_iff_exists_Ioo_subset] at hev
  obtain ⟨u, hu1, hu⟩ := hev
  have hu1' : 1 < u := mem_Ioi.1 hu1
  set x₀ := (1 + u) / 2 with hx₀
  have hx₀1 : 1 < x₀ := by rw [hx₀]; linarith
  have hx₀u : x₀ < u := by rw [hx₀]; linarith

  have hgb : ∀ t, 1 < t → t < x₀ → (δ - e) / (t - 1) ≤ g t ∧ g t ≤ (δ + e) / (t - 1) := by
    intro t ht1 ht2
    have ht : t ∈ Ioo 1 u := ⟨ht1, by linarith⟩
    have hd := hu ht
    simp only [mem_ofPred_eq, Real.dist_eq] at hd
    rw [abs_lt] at hd
    have hpos : 0 < t - 1 := sub_pos.2 ht1
    constructor
    · rw [div_le_iff₀ hpos]; linarith
    · rw [le_div_iff₀ hpos]; linarith

  have hmono : MonotoneOn (fun t => f t + (δ + e) * Real.log (t - 1)) (Ioc 1 x₀) := by
    have hd : ∀ t, 1 < t → HasDerivAt (fun t => f t + (δ + e) * Real.log (t - 1))
        (-g t + (δ + e) * (1 / (t - 1))) t :=
      fun t ht => (hder t ht).add ((hlogder t ht).const_mul (δ + e))
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 1 x₀)
      (fun t ht => (hd t ht.1).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (by rw [interior_Ioc] at ht; exact ht.1)).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Ioc] at ht
    have := (hgb t ht.1 ht.2).2
    rw [mul_one_div]
    linarith
  have hanti : AntitoneOn (fun t => f t + (δ - e) * Real.log (t - 1)) (Ioc 1 x₀) := by
    have hd : ∀ t, 1 < t → HasDerivAt (fun t => f t + (δ - e) * Real.log (t - 1))
        (-g t + (δ - e) * (1 / (t - 1))) t :=
      fun t ht => (hder t ht).add ((hlogder t ht).const_mul (δ - e))
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ioc 1 x₀)
      (fun t ht => (hd t ht.1).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (by rw [interior_Ioc] at ht; exact ht.1)).hasDerivWithinAt) ?_
    intro t ht
    rw [interior_Ioc] at ht
    have := (hgb t ht.1 ht.2).1
    rw [mul_one_div]
    linarith
  set Cp := f x₀ + (δ + e) * Real.log (x₀ - 1) with hCp
  set Cm := f x₀ + (δ - e) * Real.log (x₀ - 1) with hCm
  have hx₀mem : x₀ ∈ Ioc 1 x₀ := ⟨hx₀1, le_rfl⟩
  have hup : ∀ x, 1 < x → x < x₀ → f x ≤ Cp + (δ + e) * L x := by
    intro x h1 h2
    have := hmono ⟨h1, h2.le⟩ hx₀mem h2.le
    simp only at this
    rw [hLeq]; linarith
  have hlo : ∀ x, 1 < x → x < x₀ → Cm + (δ - e) * L x ≤ f x := by
    intro x h1 h2
    have := hanti ⟨h1, h2.le⟩ hx₀mem h2.le
    simp only at this
    rw [hLeq]; linarith
  have hnear : Ioo 1 x₀ ∈ 𝓝[>] (1:ℝ) := Ioo_mem_nhdsGT hx₀1
  have hLpos : ∀ᶠ x in 𝓝[>] (1:ℝ), 0 < L x := hL.eventually (eventually_gt_atTop 0)
  have hcp : ∀ᶠ x in 𝓝[>] (1:ℝ), |Cp| / L x < e :=
    (tendsto_const_nhds.div_atTop hL).eventually (gt_mem_nhds he0)
  have hcm : ∀ᶠ x in 𝓝[>] (1:ℝ), |Cm| / L x < e :=
    (tendsto_const_nhds.div_atTop hL).eventually (gt_mem_nhds he0)
  filter_upwards [hnear, hLpos, hcp, hcm] with x hx hLp hcpx hcmx
  have h1 := hup x hx.1 hx.2
  have h2 := hlo x hx.1 hx.2
  have hcp' : |Cp| < e * L x := by rw [div_lt_iff₀ hLp] at hcpx; linarith
  have hcm' : |Cm| < e * L x := by rw [div_lt_iff₀ hLp] at hcmx; linarith
  have hq : f x = (f x / L x) * L x := by field_simp
  have hupper : (f x / L x) * L x < (δ + 2 * e) * L x := by
    rw [← hq]; nlinarith [le_abs_self Cp]
  have hlower : (δ - 2 * e) * L x < (f x / L x) * L x := by
    rw [← hq]; nlinarith [neg_abs_le Cm]
  have hu' := lt_of_mul_lt_mul_right hupper hLp.le
  have hl' := lt_of_mul_lt_mul_right hlower hLp.le
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

end Formalism.HF.P

namespace Formalism.HF

/- English proof (authored)
Apply the conversion from logarithmic density to Dirichlet density to the given set S and its logarithmic density δ. The converted density has the same value δ.
-/
theorem logToDir : LogToDir := fun S δ h => Formalism.HF.P.dirichlet_density_of_log_density S δ h

end Formalism.HF
