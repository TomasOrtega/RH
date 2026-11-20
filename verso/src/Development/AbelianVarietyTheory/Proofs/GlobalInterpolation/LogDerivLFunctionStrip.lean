import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SummableNinePowMulInvSqSucc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TsumOneDivRpowLe
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOneSubConjMul
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.LWide

/- English proof (translation)
Take `⟨C, hC, H⟩` from `LogDerivZeros.main r R hr hrR hR`. Use `⟨C, hC, fun F c a M ha hF hc hM => ?_⟩` and prove the remaining obligations. Establish `hac : (a : ℂ) ≠ 0` using `by exact_mod_cast ha.ne'`. Use `set φ : ℂ → ℂ := fun z => c + a * z with hφ`. Establish `hφn : ∀ z, ‖φ z - c‖ = a * ‖z‖` using `fun z => by`.

Simplify using `[hφ, abs_of_pos ha]`. Establish `hφd : ∀ z, HasDerivAt φ a z` using `fun z => by`. Simplify `((hasDerivAt_id z).const_mul (a : ℂ)).const_add c` using `[hφ]`. Establish `hφa : ∀ z, AnalyticAt ℂ φ z` using `fun z => by`. Simplify using `only [hφ]`.

Use `fun_prop`. Establish `hφ0 : φ 0 = c` using `by simp [hφ]`. Establish `hinj : Function.Injective φ` using `fun x y h => by`. Simplify `h` using `[hφ, hac]`. Establish `hsurj : ∀ w, φ ((w - c) / a) = w` using `fun w => by`.

Simplify using `only [hφ]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Take `⟨⟨h1, h2⟩, h3⟩` from `H (F ∘ φ) M (fun z _ => (hF.analyticAt _).comp (hφa z)) (by simpa [hφ0] using hc) (fun z hz => hM _ (by`. Rewrite using `[hφn]; exact mul_le_of_le_one_right ha.le (by simpa using hz)))`.

Establish `hset : {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0} = φ '' {w : ℂ | ‖w‖ ≤ R ∧ (F ∘ φ) w = 0}`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hw, hw0⟩`. Use `⟨(w - c) / a, ⟨?_, by simpa [hsurj] using hw0⟩, hsurj w⟩` and prove the remaining obligations.

Rewrite using `[norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le, div_le_iff₀ ha]`. Conclude with `hw`. Introduce and unpack `⟨z, ⟨hz, hz0⟩, rfl⟩`. Use `⟨?_, hz0⟩` and prove the remaining obligations. Rewrite using `[hφn, mul_comm]`.

Use `gcongr`. Establish `hord : ∀ z, analyticOrderNatAt (F ∘ φ) z = analyticOrderNatAt F (φ z)` using `fun z => by`. Unfold `analyticOrderNatAt`. Rewrite using `[analyticOrderAt_comp_of_deriv_ne_zero (hφa z) (by rw [(hφd z).deriv]; exact hac)]`. Simplify using `only [hord, Function.comp_apply (f := F) (g := φ) (x := 0), hφ0] at h2 h3`.

Rewrite using `[hset]`. Use `⟨h1.image _, ?_, fun s hs hs0 => ?_⟩` and prove the remaining obligations. Rewrite using `[finsum_mem_image hinj.injOn]`. Conclude with `h2`. Take `⟨z, rfl⟩ : ∃ z, φ z = s` from `⟨_, hsurj s⟩`.

Rewrite using `[finsum_mem_image hinj.injOn]`. Rewrite `hs` using `[hφn, mul_comm]`. Establish `h4` using `h3 z (le_of_mul_le_mul_right hs ha) hs0`. Use `le_trans (le_of_eq ?_) h4` and prove the remaining obligations. Establish `hd : deriv (F ∘ φ) z = deriv F (φ z) * a` using `((hF (φ z)).hasDerivAt.comp z (hφd z)).deriv`.

Rewrite using `[hd, finsum_mem_eq_finite_toFinset_sum _ h1, finsum_mem_eq_finite_toFinset_sum _ h1]`. Use `conv_lhs => rw [← Real.norm_of_nonneg ha.le, ← Complex.norm_real, ← norm_mul]`. Use `congr 1`. Rewrite using `[mul_sub, Finset.mul_sum]`. Use `congr 1`.

Simplify using `only [Function.comp_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `: φ z - φ w = a * (z - w)` using `by simp only [hφ]; ring`. Rewrite using `[this, ← mul_div_assoc, mul_div_mul_left _ _ hac]`.
-/
theorem disc (r R : ℝ) (hr : 0 < r) (hrR : r < R) (hR : R < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : ℂ → ℂ) (c : ℂ) (a M : ℝ), 0 < a → Differentiable ℂ F → F c ≠ 0 →
      (∀ z, ‖z - c‖ ≤ a → ‖F z‖ ≤ M) →
      {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0}.Finite ∧
      (∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0}, (analyticOrderNatAt F w : ℝ))
        ≤ C * (1 + Real.log (M / ‖F c‖)) ∧
      ∀ s : ℂ, ‖s - c‖ ≤ r * a → F s ≠ 0 →
        a * ‖deriv F s / F s - ∑ᶠ w ∈ {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0},
          (analyticOrderNatAt F w : ℂ) / (s - w)‖ ≤ C * (1 + Real.log (M / ‖F c‖)) := by
  obtain ⟨C, hC, H⟩ := LogDerivZeros.main r R hr hrR hR
  refine ⟨C, hC, fun F c a M ha hF hc hM => ?_⟩
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  set φ : ℂ → ℂ := fun z => c + a * z with hφ
  have hφn : ∀ z, ‖φ z - c‖ = a * ‖z‖ := fun z => by
    simp [hφ, abs_of_pos ha]
  have hφd : ∀ z, HasDerivAt φ a z := fun z => by
    simpa [hφ] using ((hasDerivAt_id z).const_mul (a : ℂ)).const_add c
  have hφa : ∀ z, AnalyticAt ℂ φ z := fun z => by
    simp only [hφ]; fun_prop
  have hφ0 : φ 0 = c := by simp [hφ]
  have hinj : Function.Injective φ := fun x y h => by
    simpa [hφ, hac] using h
  have hsurj : ∀ w, φ ((w - c) / a) = w := fun w => by
    simp only [hφ]; field_simp; ring
  obtain ⟨⟨h1, h2⟩, h3⟩ := H (F ∘ φ) M
    (fun z _ => (hF.analyticAt _).comp (hφa z)) (by simpa [hφ0] using hc)
    (fun z hz => hM _ (by
      rw [hφn]; exact mul_le_of_le_one_right ha.le (by simpa using hz)))
  have hset : {w : ℂ | ‖w - c‖ ≤ R * a ∧ F w = 0} = φ '' {w : ℂ | ‖w‖ ≤ R ∧ (F ∘ φ) w = 0} := by
    ext w
    constructor
    · rintro ⟨hw, hw0⟩
      refine ⟨(w - c) / a, ⟨?_, by simpa [hsurj] using hw0⟩, hsurj w⟩
      rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le, div_le_iff₀ ha]
      exact hw
    · rintro ⟨z, ⟨hz, hz0⟩, rfl⟩
      refine ⟨?_, hz0⟩
      rw [hφn, mul_comm]
      gcongr
  have hord : ∀ z, analyticOrderNatAt (F ∘ φ) z = analyticOrderNatAt F (φ z) := fun z => by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_comp_of_deriv_ne_zero (hφa z) (by rw [(hφd z).deriv]; exact hac)]
  simp only [hord, Function.comp_apply (f := F) (g := φ) (x := 0), hφ0] at h2 h3
  rw [hset]
  refine ⟨h1.image _, ?_, fun s hs hs0 => ?_⟩
  · rw [finsum_mem_image hinj.injOn]
    exact h2
  · obtain ⟨z, rfl⟩ : ∃ z, φ z = s := ⟨_, hsurj s⟩
    rw [finsum_mem_image hinj.injOn]
    rw [hφn, mul_comm] at hs
    have h4 := h3 z (le_of_mul_le_mul_right hs ha) hs0
    refine le_trans (le_of_eq ?_) h4
    have hd : deriv (F ∘ φ) z = deriv F (φ z) * a :=
      ((hF (φ z)).hasDerivAt.comp z (hφd z)).deriv
    rw [hd, finsum_mem_eq_finite_toFinset_sum _ h1, finsum_mem_eq_finite_toFinset_sum _ h1]
    conv_lhs => rw [← Real.norm_of_nonneg ha.le, ← Complex.norm_real, ← norm_mul]
    congr 1
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · simp only [Function.comp_apply]; ring
    · refine Finset.sum_congr rfl fun w _ => ?_
      have : φ z - φ w = a * (z - w) := by simp only [hφ]; ring
      rw [this, ← mul_div_assoc, mul_div_mul_left _ _ hac]

/- English proof (translation)
Take `⟨C, hC, H⟩` from `disc (4 / 5) (14 / 15) (by norm_num) (by norm_num) (by norm_num)`. Take `⟨B, hB, G⟩` from `norm_LFunction_le_poly_left`. Use `⟨C * (2 * (1 + |Real.log (512 * B)|) + 4), by positivity, ?_⟩` and prove the remaining obligations. Introduce `q _ χ hχ s hs1 hs2 hs0`. Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)`.

Use `set c : ℂ := 2 + s.im * I with hc`. Establish `hcre : c.re = 2` using `by simp [hc]`. Establish `hcn : ‖c‖ ≤ 2 + |s.im|`. Use `(norm_add_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `hlow : 1 / 2 ≤ ‖LFunction χ c‖`. Use `LLower.norm_LFunction_ge q χ c (by rw [hcre]; norm_num)` as an intermediate fact. Rewrite `this` using `[hcre]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht` using `abs_nonneg s.im`.

Use `set X : ℝ := q * (|s.im| + 2) with hX`. Establish `hX2 : 2 ≤ X` using `by nlinarith`. Establish `hlX : 1 / 2 ≤ Real.log X`. Use `Real.log_le_log (by norm_num) hX2` as an intermediate fact. Combine the linear relations using `[Real.log_two_gt_d9]`.

Establish `hpos : 0 < ‖LFunction χ c‖` using `by linarith`. Take `⟨h1, h2, h3⟩` from `H (LFunction χ) c (15 / 4) (256 * B * X ^ 4) (by norm_num) (differentiable_LFunction hχ) (norm_pos_iff.1 hpos) (fun z hz => by`. Establish `hre : -(7 / 4 : ℝ) ≤ z.re`. Use `(abs_le.1 ((Complex.abs_re_le_norm (z - c)).trans hz)).1` as an intermediate fact. Rewrite `this` using `[sub_re, hcre]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `(G q χ hχ z hre).trans ?_` and prove the remaining obligations. Establish `hzn : ‖z‖ + 2 ≤ 4 * (|s.im| + 2)`. Use `norm_le_norm_sub_add z c` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Combine the equalities or inequalities in the displayed calculation. Establish `e : (14 / 15 : ℝ) * (15 / 4) = 7 / 2` using `by norm_num`. Rewrite `h1`, `h2`, `h3` using `[e]`. Establish `hsc : ‖s - c‖ ≤ 4 / 5 * (15 / 4)`. Establish `: s - c = ((s.re - 2 : ℝ) : ℂ)`.

Apply the tactic sequence `apply Complex.ext <;> simp [hc]`. Rewrite using `[this, Complex.norm_real, Real.norm_eq_abs, abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Establish `h4` using `h3 s hsc hs0`. Establish `hlog : Real.log (256 * B * X ^ 4 / ‖LFunction χ c‖) ≤ Real.log (512 * B) + 4 * Real.log X`.

Establish `hX0 : 0 < X` using `by linarith`. Establish `: 256 * B * X ^ 4 / ‖LFunction χ c‖ ≤ 512 * B * X ^ 4`. Rewrite using `[div_le_iff₀ hpos]`. Establish `: 0 < B * X ^ 4` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Use `(Real.log_le_log (by positivity) this).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Real.log_mul (by positivity) (by positivity), Real.log_pow]`. Evaluate the numerical expressions. Establish `hfin : C * (1 + Real.log (256 * B * X ^ 4 / ‖LFunction χ c‖)) ≤ C * (2 * (1 + |Real.log (512 * B)|) + 4) * Real.log X`. Rewrite using `[mul_assoc C]`.

Use `mul_le_mul_of_nonneg_left ?_ hC.le` and prove the remaining obligations. Establish `h5` using `le_abs_self (Real.log (512 * B))`. Establish `h6` using `abs_nonneg (Real.log (512 * B))`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨h1, h2.trans hfin, le_trans ?_ (h4.trans hfin)⟩` and prove the remaining obligations.

Conclude with `le_mul_of_one_le_left (norm_nonneg _) (by norm_num)`.
-/
theorem logDeriv_LFunction_strip : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 → ∀ s : ℂ, -1 ≤ s.re → s.re ≤ 2 → LFunction χ s ≠ 0 → {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ LFunction χ w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℝ)) ≤ C * Real.log (q * (|s.im| + 2)) ∧ ‖deriv (LFunction χ) s / LFunction χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (2 + s.im * I)‖ ≤ 7/2 ∧ LFunction χ w = 0}, (analyticOrderNatAt (LFunction χ) w : ℂ) / (s - w)‖ ≤ C * Real.log (q * (|s.im| + 2)) := by
  obtain ⟨C, hC, H⟩ := disc (4 / 5) (14 / 15) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨B, hB, G⟩ := norm_LFunction_le_poly_left
  refine ⟨C * (2 * (1 + |Real.log (512 * B)|) + 4), by positivity, ?_⟩
  intro q _ χ hχ s hs1 hs2 hs0
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  set c : ℂ := 2 + s.im * I with hc
  have hcre : c.re = 2 := by simp [hc]
  have hcn : ‖c‖ ≤ 2 + |s.im| := by
    refine (norm_add_le _ _).trans (le_of_eq ?_)
    simp
  have hlow : 1 / 2 ≤ ‖LFunction χ c‖ := by
    have := LLower.norm_LFunction_ge q χ c (by rw [hcre]; norm_num)
    rw [hcre] at this
    linarith
  have ht := abs_nonneg s.im
  set X : ℝ := q * (|s.im| + 2) with hX
  have hX2 : 2 ≤ X := by nlinarith
  have hlX : 1 / 2 ≤ Real.log X := by
    have := Real.log_le_log (by norm_num) hX2
    linarith [Real.log_two_gt_d9]
  have hpos : 0 < ‖LFunction χ c‖ := by linarith
  obtain ⟨h1, h2, h3⟩ := H (LFunction χ) c (15 / 4) (256 * B * X ^ 4) (by norm_num)
    (differentiable_LFunction hχ) (norm_pos_iff.1 hpos) (fun z hz => by
      have hre : -(7 / 4 : ℝ) ≤ z.re := by
        have := (abs_le.1 ((Complex.abs_re_le_norm (z - c)).trans hz)).1
        rw [sub_re, hcre] at this
        linarith
      refine (G q χ hχ z hre).trans ?_
      have hzn : ‖z‖ + 2 ≤ 4 * (|s.im| + 2) := by
        have := norm_le_norm_sub_add z c
        linarith
      calc B * (q : ℝ) ^ 4 * (‖z‖ + 2) ^ 4 ≤ B * (q : ℝ) ^ 4 * (4 * (|s.im| + 2)) ^ 4 := by gcongr
        _ = _ := by rw [hX]; ring)
  have e : (14 / 15 : ℝ) * (15 / 4) = 7 / 2 := by norm_num
  rw [e] at h1 h2 h3
  have hsc : ‖s - c‖ ≤ 4 / 5 * (15 / 4) := by
    have : s - c = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have h4 := h3 s hsc hs0
  have hlog : Real.log (256 * B * X ^ 4 / ‖LFunction χ c‖) ≤ Real.log (512 * B) + 4 * Real.log X := by
    have hX0 : 0 < X := by linarith
    have : 256 * B * X ^ 4 / ‖LFunction χ c‖ ≤ 512 * B * X ^ 4 := by
      rw [div_le_iff₀ hpos]
      have : 0 < B * X ^ 4 := by positivity
      nlinarith
    refine (Real.log_le_log (by positivity) this).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  have hfin : C * (1 + Real.log (256 * B * X ^ 4 / ‖LFunction χ c‖))
      ≤ C * (2 * (1 + |Real.log (512 * B)|) + 4) * Real.log X := by
    rw [mul_assoc C]
    refine mul_le_mul_of_nonneg_left ?_ hC.le
    have h5 := le_abs_self (Real.log (512 * B))
    have h6 := abs_nonneg (Real.log (512 * B))
    nlinarith
  refine ⟨h1, h2.trans hfin, le_trans ?_ (h4.trans hfin)⟩
  exact le_mul_of_one_le_left (norm_nonneg _) (by norm_num)

end GlobalTheory.LWide
