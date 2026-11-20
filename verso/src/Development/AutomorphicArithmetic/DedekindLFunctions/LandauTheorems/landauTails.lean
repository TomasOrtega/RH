import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.kernelIntegral

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Assume the negation of the conclusion as `h`. Establish `h1` using `kernel_integral k a ha`. Rewrite `h1` using `[integral_undef h]`. Establish `: 0 < (a ^ (k + 1))⁻¹` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma landau_tails_integrable (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => u ^ k * Real.exp (-a * u) / (k.factorial : ℝ)) (Ioi 0) := by
  by_contra h
  have h1 := kernel_integral k a ha
  rw [integral_undef h] at h1
  have : 0 < (a ^ (k + 1))⁻¹ := by positivity
  linarith

/- English proof (translation)
Establish `ha : 0 < s - l` using `by linarith`. Establish `hb : 0 < s + l` using `by linarith`. Establish `hs0 : 0 < s` using `by linarith`. Establish `i1` using `(landau_tails_integrable k ha).const_mul (Real.exp (-(l * V)))`. Establish `i2` using `(landau_tails_integrable k hb).const_mul (Real.exp (l * U))`.

Establish `i0` using `landau_tails_integrable k hs0`. Establish `i3` using `i1.add i2`. Rewrite using `[← kernel_integral k _ ha, ← kernel_integral k _ hb, ← integral_const_mul, ← integral_const_mul, ← integral_add i1 i2]`. Establish `hm : MeasurableSet (Ioi (0 : ℝ) \ Icc U V)` using `measurableSet_Ioi.diff measurableSet_Icc`. Use `le_trans (setIntegral_mono_on (IntegrableOn.mono_set i0 sdiff_subset) (IntegrableOn.mono_set i3 sdiff_subset) hm ?_) (setIntegral_mono_set i3 ?_ sdiff_subset.eventuallyLE)` and prove the remaining obligations.

Introduce `u hu`. Establish `hu0 : 0 < u` using `hu.1`. Establish `hf : 0 < (k.factorial : ℝ)` using `by positivity`. Establish `hp : 0 ≤ u ^ k / (k.factorial : ℝ)` using `by positivity`. Establish `e1 : Real.exp (-(l * V)) * Real.exp (-(s - l) * u) = Real.exp (-s * u + l * (u - V))`.

Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : Real.exp (l * U) * Real.exp (-(s + l) * u) = Real.exp (-s * u + l * (U - u))`. Rewrite using `[← Real.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `key : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (u - V)) + Real.exp (-s * u + l * (U - u))`. Establish `hn` using `hu.2`. Rewrite `hn` using `[mem_Icc, not_and_or, not_le, not_le]`.

Break down `hn with h | h` into its components or cases. Establish `: Real.exp (-s * u) ≤ Real.exp (-s * u + l * (U - u))` using `Real.exp_le_exp.2 (by nlinarith [mul_nonneg hl (sub_nonneg.2 h.le)])`. Combine the linear relations using `[Real.exp_pos (-s * u + l * (u - V))]`. Establish `: Real.exp (-s * u) ≤ Real.exp (-s * u + l * (u - V))` using `Real.exp_le_exp.2 (by nlinarith [mul_nonneg hl (sub_nonneg.2 h.le)])`. Combine the linear relations using `[Real.exp_pos (-s * u + l * (U - u))]`.

Rewrite `key` using `[← e1, ← e2]`. Use `mul_le_mul_of_nonneg_left key hp` as an intermediate fact. Simplify using `only [Pi.add_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu`.

Establish `hu0 : 0 < u` using `hu`. Simplify using `only [Pi.add_apply, Pi.zero_apply]`. Check the signs of the components of the expression.
-/
lemma landau_tails_chernoff (k : ℕ) {s l U V : ℝ} (hl : 0 ≤ l) (hs : l < s) :
    ∫ u in Ioi (0 : ℝ) \ Icc U V, u ^ k * Real.exp (-s * u) / (k.factorial : ℝ) ≤
      Real.exp (-(l * V)) * ((s - l) ^ (k + 1))⁻¹ + Real.exp (l * U) * ((s + l) ^ (k + 1))⁻¹ := by
  have ha : 0 < s - l := by linarith
  have hb : 0 < s + l := by linarith
  have hs0 : 0 < s := by linarith
  have i1 := (landau_tails_integrable k ha).const_mul (Real.exp (-(l * V)))
  have i2 := (landau_tails_integrable k hb).const_mul (Real.exp (l * U))
  have i0 := landau_tails_integrable k hs0
  have i3 := i1.add i2
  rw [← kernel_integral k _ ha, ← kernel_integral k _ hb, ← integral_const_mul, ← integral_const_mul,
    ← integral_add i1 i2]
  have hm : MeasurableSet (Ioi (0 : ℝ) \ Icc U V) := measurableSet_Ioi.diff measurableSet_Icc
  refine le_trans (setIntegral_mono_on (IntegrableOn.mono_set i0 sdiff_subset)
    (IntegrableOn.mono_set i3 sdiff_subset) hm ?_) (setIntegral_mono_set i3 ?_ sdiff_subset.eventuallyLE)
  · intro u hu
    have hu0 : 0 < u := hu.1
    have hf : 0 < (k.factorial : ℝ) := by positivity
    have hp : 0 ≤ u ^ k / (k.factorial : ℝ) := by positivity
    have e1 : Real.exp (-(l * V)) * Real.exp (-(s - l) * u) = Real.exp (-s * u + l * (u - V)) := by
      rw [← Real.exp_add]; congr 1; ring
    have e2 : Real.exp (l * U) * Real.exp (-(s + l) * u) = Real.exp (-s * u + l * (U - u)) := by
      rw [← Real.exp_add]; congr 1; ring
    have key : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (u - V)) + Real.exp (-s * u + l * (U - u)) := by
      have hn := hu.2
      rw [mem_Icc, not_and_or, not_le, not_le] at hn
      rcases hn with h | h
      · have : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (U - u)) :=
          Real.exp_le_exp.2 (by nlinarith [mul_nonneg hl (sub_nonneg.2 h.le)])
        linarith [Real.exp_pos (-s * u + l * (u - V))]
      · have : Real.exp (-s * u) ≤ Real.exp (-s * u + l * (u - V)) :=
          Real.exp_le_exp.2 (by nlinarith [mul_nonneg hl (sub_nonneg.2 h.le)])
        linarith [Real.exp_pos (-s * u + l * (U - u))]
    rw [← e1, ← e2] at key
    have := mul_le_mul_of_nonneg_left key hp
    simp only [Pi.add_apply]
    calc _ = u ^ k / (k.factorial : ℝ) * Real.exp (-s * u) := by ring
      _ ≤ _ := this
      _ = _ := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := hu
    simp only [Pi.add_apply, Pi.zero_apply]
    positivity

/- English proof (translation)
Establish `h1 : σ / a ≤ Real.exp ((σ - a) / a)`. Use `Real.add_one_le_exp ((σ - a) / a)` as an intermediate fact. Establish `e : (σ - a) / a + 1 = σ / a` using `by field_simp; ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (σ / a) ^ k ≤ Real.exp (k * ((σ - a) / a))`.

Rewrite using `[Real.exp_nat_mul]`. Conclude with `pow_le_pow_left₀ (by positivity) h1 k`. Establish `h3 : Real.exp x * (σ / a) ^ k ≤ Real.exp c`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[div_pow, pow_succ]`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ _ := by gcongr`.
-/
lemma landau_tails_pow (k : ℕ) {σ a x c : ℝ} (hσ : 0 < σ) (ha : 0 < a)
    (h : x + k * ((σ - a) / a) ≤ c) :
    Real.exp x * (a ^ (k + 1))⁻¹ ≤ Real.exp c / a / σ ^ k := by
  have h1 : σ / a ≤ Real.exp ((σ - a) / a) := by
    have := Real.add_one_le_exp ((σ - a) / a)
    have e : (σ - a) / a + 1 = σ / a := by field_simp; ring
    linarith
  have h2 : (σ / a) ^ k ≤ Real.exp (k * ((σ - a) / a)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) h1 k
  have h3 : Real.exp x * (σ / a) ^ k ≤ Real.exp c := by
    calc _ ≤ Real.exp x * Real.exp (k * ((σ - a) / a)) := by gcongr
      _ = Real.exp (x + k * ((σ - a) / a)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.2 h
  calc _ = Real.exp x * (σ / a) ^ k / a / σ ^ k := by
        rw [div_pow, pow_succ]; field_simp
    _ ≤ _ := by gcongr

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨l, hl2, hl⟩ : ∃ l : ℝ, 2 < l ∧ l * δ = 6 + 2 * δ := by`. Use `⟨2 + 6 / δ, by have : 0 < 6 / δ := by positivity linarith, by field_simp; ring⟩` and prove the remaining obligations. Take `⟨M, hM⟩ : ∃ M : ℝ, M = l * (1 + δ)` from `⟨_, rfl⟩`. Establish `hMl : l < M` using `by nlinarith`. Take `⟨σ, hσ⟩ : ∃ σ : ℝ, σ = M * (2 + l)` from `⟨_, rfl⟩`.

Establish `hσ1 : l * (2 + l) < σ` using `by rw [hσ]; gcongr`. Establish `hs : l < σ - 2` using `by nlinarith`. Establish `ha : 0 < σ - 2 - l` using `by linarith`. Establish `hb : 0 < σ - 2 + l` using `by linarith`. Establish `hσ0 : 0 < σ` using `by linarith`.

Use `⟨σ, by linarith, Real.exp 1 / (σ - 2 - l) + Real.exp 0 / (σ - 2 + l), fun U hU => ?_⟩` and prove the remaining obligations. Establish `hx : 0 ≤ (1 + δ / 2) * σ * U` using `by positivity`. Establish `hk1` using `Nat.le_ceil ((1 + δ / 2) * σ * U)`. Establish `hk2` using `(Nat.ceil_lt_add_one hx).le`. Use `set k := ⌈(1 + δ / 2) * σ * U⌉₊`.

Establish `hσU : 0 ≤ σ * U` using `by positivity`. Use `⟨k, ?_, ?_⟩` and prove the remaining obligations. Use polynomial arithmetic with `[mul_nonneg hδ.le hσU]`. Establish `e : (2 - σ) = -(σ - 2)` using `by ring`. Rewrite using `[e, add_div]`.

Use `(landau_tails_chernoff k (by linarith : 0 ≤ l) hs).trans (add_le_add ?_ ?_)` and prove the remaining obligations. Apply `landau_tails_pow k hσ0 ha` to reduce the goal to its premises. Establish `e1 : (σ - (σ - 2 - l)) / (σ - 2 - l) = 1 / (M - 1)`. Establish `: 0 < M - 1` using `by linarith`. Rewrite using `[div_eq_div_iff ha.ne' this.ne', hσ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (1 + δ / 2) * σ = M * (M - 1)`. Establish `: (1 + δ / 2) * (2 + l) = M - 1` using `by rw [hM]; nlinarith`. Rewrite using `[hσ, ← this]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hM1 : 1 ≤ M - 1` using `by linarith`. Establish `e3 : (k : ℝ) * (1 / (M - 1)) ≤ M * U + 1`. Rewrite using `[mul_one_div, div_le_iff₀ (by linarith)]`. Rewrite `hk2` using `[e2]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `e4 : l * ((1 + δ) * U) = M * U` using `by rw [hM]; ring`. Rewrite using `[e1, e4]`. Combine the linear equalities and inequalities to obtain the conclusion. Apply `landau_tails_pow k hσ0 hb` to reduce the goal to its premises. Establish `e1 : (k : ℝ) * ((σ - (σ - 2 + l)) / (σ - 2 + l)) = -((k : ℝ) * (l - 2) / (σ - 2 + l))`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (1 + δ / 2) * (l - 2) = l + 1` using `by nlinarith`. Establish `e3 : l * U ≤ (k : ℝ) * (l - 2) / (σ - 2 + l)`. Rewrite using `[le_div_iff₀ hb]`. Establish `h1 : (1 + δ / 2) * σ * U * (l - 2) ≤ k * (l - 2)` using `mul_le_mul_of_nonneg_right hk1 (by linarith)`.

Establish `h2 : (1 + δ / 2) * σ * U * (l - 2) = (l + 1) * σ * U` using `by rw [← e2]; ring`. Establish `h3 : l * (σ - 2 + l) ≤ (l + 1) * σ` using `by nlinarith`. Establish `h4` using `mul_le_mul_of_nonneg_right h3 (by linarith : 0 ≤ U)`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[e1]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem landau_tails {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, ∀ U : ℝ, 1 ≤ U → ∃ k : ℕ, U ≤ k ∧
      ∫ u in Ioi (0 : ℝ) \ Icc U ((1 + δ) * U), u ^ k * Real.exp ((2 - σ) * u) / (k.factorial : ℝ) ≤ C / σ ^ k := by
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℝ, 2 < l ∧ l * δ = 6 + 2 * δ := by
    refine ⟨2 + 6 / δ, by have : 0 < 6 / δ := by positivity
                          linarith, by field_simp; ring⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = l * (1 + δ) := ⟨_, rfl⟩
  have hMl : l < M := by nlinarith
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = M * (2 + l) := ⟨_, rfl⟩
  have hσ1 : l * (2 + l) < σ := by rw [hσ]; gcongr
  have hs : l < σ - 2 := by nlinarith
  have ha : 0 < σ - 2 - l := by linarith
  have hb : 0 < σ - 2 + l := by linarith
  have hσ0 : 0 < σ := by linarith
  refine ⟨σ, by linarith, Real.exp 1 / (σ - 2 - l) + Real.exp 0 / (σ - 2 + l), fun U hU => ?_⟩
  have hx : 0 ≤ (1 + δ / 2) * σ * U := by positivity
  have hk1 := Nat.le_ceil ((1 + δ / 2) * σ * U)
  have hk2 := (Nat.ceil_lt_add_one hx).le
  set k := ⌈(1 + δ / 2) * σ * U⌉₊
  have hσU : 0 ≤ σ * U := by positivity
  refine ⟨k, ?_, ?_⟩
  · nlinarith [mul_nonneg hδ.le hσU]
  · have e : (2 - σ) = -(σ - 2) := by ring
    rw [e, add_div]
    refine (landau_tails_chernoff k (by linarith : 0 ≤ l) hs).trans (add_le_add ?_ ?_)
    · apply landau_tails_pow k hσ0 ha
      have e1 : (σ - (σ - 2 - l)) / (σ - 2 - l) = 1 / (M - 1) := by
        have : 0 < M - 1 := by linarith
        rw [div_eq_div_iff ha.ne' this.ne', hσ]; ring
      have e2 : (1 + δ / 2) * σ = M * (M - 1) := by
        have : (1 + δ / 2) * (2 + l) = M - 1 := by rw [hM]; nlinarith
        rw [hσ, ← this]; ring
      have hM1 : 1 ≤ M - 1 := by linarith
      have e3 : (k : ℝ) * (1 / (M - 1)) ≤ M * U + 1 := by
        rw [mul_one_div, div_le_iff₀ (by linarith)]
        rw [e2] at hk2
        nlinarith
      have e4 : l * ((1 + δ) * U) = M * U := by rw [hM]; ring
      rw [e1, e4]; linarith
    · apply landau_tails_pow k hσ0 hb
      have e1 : (k : ℝ) * ((σ - (σ - 2 + l)) / (σ - 2 + l)) = -((k : ℝ) * (l - 2) / (σ - 2 + l)) := by
        ring
      have e2 : (1 + δ / 2) * (l - 2) = l + 1 := by nlinarith
      have e3 : l * U ≤ (k : ℝ) * (l - 2) / (σ - 2 + l) := by
        rw [le_div_iff₀ hb]
        have h1 : (1 + δ / 2) * σ * U * (l - 2) ≤ k * (l - 2) :=
          mul_le_mul_of_nonneg_right hk1 (by linarith)
        have h2 : (1 + δ / 2) * σ * U * (l - 2) = (l + 1) * σ * U := by rw [← e2]; ring
        have h3 : l * (σ - 2 + l) ≤ (l + 1) * σ := by nlinarith
        have h4 := mul_le_mul_of_nonneg_right h3 (by linarith : 0 ≤ U)
        nlinarith
      rw [e1]; linarith

end Deduction

end
