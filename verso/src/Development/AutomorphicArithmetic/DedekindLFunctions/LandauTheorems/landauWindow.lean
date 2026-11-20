import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauCauchy
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauPoleAsym
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauTails
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauKernelMax
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.landauWindowIneq
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauPoleReLe
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauCoeff
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauFinite
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauNearest
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauDichotomy
import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.LandauGrowthContra

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Take `⟨η, hη, U₀, hU₀⟩` from `landau_growth_contra (C := |M| + |C|) hc hd hde`. Take `⟨U, hU, k, hk, hle⟩` from `H η hη (max U₀ 0)`. Establish `h1` using `hU₀ U ((le_max_left _ _).trans hU) k hk`. Establish `hU0 : 0 ≤ U` using `(le_max_right _ _).trans hU`. Establish `he : 0 < e` using `hd.trans hde`.

Establish `hek : 0 < e ^ k` using `pow_pos he k`. Establish `hexp : 1 ≤ Real.exp (η * U)` using `Real.one_le_exp (by positivity)`. Establish `h2 : M / e ^ k ≤ |M| * Real.exp (η * U) / e ^ k`. Apply `div_le_div_of_nonneg_right _ hek.le` to reduce the goal to its premises. Conclude with `(le_abs_self M).trans (le_mul_of_one_le_right (abs_nonneg M) hexp)`.

Establish `h3 : C * Real.exp (η * U) / E ^ k ≤ |C| * Real.exp (η * U) / e ^ k`. Apply `div_le_div₀ (by positivity) _ hek (pow_le_pow_left₀ he.le heE k)` to reduce the goal to its premises. Conclude with `mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le`. Establish `h4 : (|M| + |C|) * Real.exp (η * U) / e ^ k = |M| * Real.exp (η * U) / e ^ k + |C| * Real.exp (η * U) / e ^ k` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem landau_window_contra {c d e E M C : ℝ} (hc : 0 < c) (hd : 0 < d) (hde : d < e) (heE : e ≤ E)
    (H : ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ k : ℕ, U ≤ k ∧
      c / d ^ k ≤ M / e ^ k + C * Real.exp (η * U) / E ^ k) : False := by
  obtain ⟨η, hη, U₀, hU₀⟩ := landau_growth_contra (C := |M| + |C|) hc hd hde
  obtain ⟨U, hU, k, hk, hle⟩ := H η hη (max U₀ 0)
  have h1 := hU₀ U ((le_max_left _ _).trans hU) k hk
  have hU0 : 0 ≤ U := (le_max_right _ _).trans hU
  have he : 0 < e := hd.trans hde
  have hek : 0 < e ^ k := pow_pos he k
  have hexp : 1 ≤ Real.exp (η * U) := Real.one_le_exp (by positivity)
  have h2 : M / e ^ k ≤ |M| * Real.exp (η * U) / e ^ k := by
    apply div_le_div_of_nonneg_right _ hek.le
    exact (le_abs_self M).trans (le_mul_of_one_le_right (abs_nonneg M) hexp)
  have h3 : C * Real.exp (η * U) / E ^ k ≤ |C| * Real.exp (η * U) / e ^ k := by
    apply div_le_div₀ (by positivity) _ hek (pow_le_pow_left₀ he.le heE k)
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le
  have h4 : (|M| + |C|) * Real.exp (η * U) / e ^ k
      = |M| * Real.exp (η * U) / e ^ k + |C| * Real.exp (η * U) / e ^ k := by ring
  linarith

/- English proof (translation)
Take `⟨σ, hσ, C, hC⟩` from `landau_tails hδ`. Take `⟨C₀, hC₀⟩` from `hP.growth`. Establish `hC₀0 : 0 ≤ C₀`. Use `hC₀ 0 le_rfl` as an intermediate fact. Simplify using `only [mul_zero, Real.exp_zero, mul_one] at this`.

Conclude with `(abs_nonneg _).trans this`. Use `⟨σ, hσ, 2 + 2 * C₀ * |C|, fun η hη U₀ => ?_⟩` and prove the remaining obligations. Take `⟨U, hU, R, hR1, hR2, hR3⟩` from `hW η hη (max U₀ 1)`. Establish `hU1 : 1 ≤ U` using `(le_max_right _ _).trans hU`. Take `⟨k, hk, hk'⟩` from `hC U hU1`.

Use `⟨U, (le_max_left _ _).trans hU, k, hk, fun γ => ?_⟩` and prove the remaining obligations. Establish `h` using `landau_window_ineq hP.meas hC₀ hσ (by linarith : θ < σ) (by linarith : 0 < U) hR1 hR2 k γ`. Rewrite using `[landau_coeff hP k (s := (σ : ℂ) + γ * I) (by simpa using hσ), landau_coeff hP k (s := (σ : ℂ)) (by simpa using hσ)]`. Establish `hst : 0 < σ - θ` using `by linarith`. Establish `hstk : 0 < (σ - θ) ^ k` using `pow_pos hst k`.

Establish `hexp : 1 ≤ Real.exp (η * U)` using `Real.one_le_exp (by positivity)`. Establish `h1 : 2 * (1 / (σ - θ) ^ k) * (∫ u in Icc U ((1 + δ) * U), R u * Real.exp (-θ * u)) ≤ 2 * (1 / (σ - θ) ^ k) * Real.exp (η * U)` using `mul_le_mul_of_nonneg_left hR3 (by positivity)`. Establish `h2 : C / σ ^ k ≤ |C| * Real.exp (η * U) / (σ - θ) ^ k`. Apply `div_le_div₀ (by positivity) _ hstk (pow_le_pow_left₀ hst.le (by linarith) k)` to reduce the goal to its premises. Conclude with `(le_abs_self C).trans (le_mul_of_one_le_right (abs_nonneg C) hexp)`.

Establish `h3` using `mul_le_mul_of_nonneg_left (hk'.trans h2) (by positivity : 0 ≤ 2 * C₀)`. Establish `h4 : (2 + 2 * C₀ * |C|) * Real.exp (η * U) / (σ - θ) ^ k = 2 * (1 / (σ - θ) ^ k) * Real.exp (η * U) + 2 * C₀ * (|C| * Real.exp (η * U) / (σ - θ) ^ k)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem landau_window_key {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hW : WindowHypU g θ δ) :
    ∃ σ : ℝ, 2 < σ ∧ ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ k : ℕ, U ≤ k ∧ ∀ γ : ℝ,
      ‖(-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + γ * I) / (k.factorial : ℂ)‖ +
        ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)).re ≤
        C * Real.exp (η * U) / (σ - θ) ^ k := by
  obtain ⟨σ, hσ, C, hC⟩ := landau_tails hδ
  obtain ⟨C₀, hC₀⟩ := hP.growth
  have hC₀0 : 0 ≤ C₀ := by
    have := hC₀ 0 le_rfl
    simp only [mul_zero, Real.exp_zero, mul_one] at this
    exact (abs_nonneg _).trans this
  refine ⟨σ, hσ, 2 + 2 * C₀ * |C|, fun η hη U₀ => ?_⟩
  obtain ⟨U, hU, R, hR1, hR2, hR3⟩ := hW η hη (max U₀ 1)
  have hU1 : 1 ≤ U := (le_max_right _ _).trans hU
  obtain ⟨k, hk, hk'⟩ := hC U hU1
  refine ⟨U, (le_max_left _ _).trans hU, k, hk, fun γ => ?_⟩
  have h := landau_window_ineq hP.meas hC₀ hσ (by linarith : θ < σ) (by linarith : 0 < U) hR1 hR2 k γ
  rw [landau_coeff hP k (s := (σ : ℂ) + γ * I) (by simpa using hσ),
    landau_coeff hP k (s := (σ : ℂ)) (by simpa using hσ)]
  have hst : 0 < σ - θ := by linarith
  have hstk : 0 < (σ - θ) ^ k := pow_pos hst k
  have hexp : 1 ≤ Real.exp (η * U) := Real.one_le_exp (by positivity)
  have h1 : 2 * (1 / (σ - θ) ^ k) * (∫ u in Icc U ((1 + δ) * U), R u * Real.exp (-θ * u))
      ≤ 2 * (1 / (σ - θ) ^ k) * Real.exp (η * U) :=
    mul_le_mul_of_nonneg_left hR3 (by positivity)
  have h2 : C / σ ^ k ≤ |C| * Real.exp (η * U) / (σ - θ) ^ k := by
    apply div_le_div₀ (by positivity) _ hstk (pow_le_pow_left₀ hst.le (by linarith) k)
    exact (le_abs_self C).trans (le_mul_of_one_le_right (abs_nonneg C) hexp)
  have h3 := mul_le_mul_of_nonneg_left (hk'.trans h2) (by positivity : 0 ≤ 2 * C₀)
  have h4 : (2 + 2 * C₀ * |C|) * Real.exp (η * U) / (σ - θ) ^ k
      = 2 * (1 / (σ - θ) ^ k) * Real.exp (η * U)
        + 2 * C₀ * (|C| * Real.exp (η * U) / (σ - θ) ^ k) := by ring
  linarith

/- English proof (translation)
Establish `h1 : ‖w - z‖ < r` using `by simpa [dist_eq_norm] using hw`. Establish `h2 : |(w - z).re| ≤ ‖w - z‖` using `Complex.abs_re_le_norm _`. Establish `h3` using `(abs_lt.mp (h2.trans_lt h1)).1`. Simplify using `only [Complex.sub_re] at h3`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem landau_window_re_pos {z w : ℂ} {r : ℝ} (hr : r ≤ z.re) (hw : w ∈ Metric.ball z r) :
    0 < w.re := by
  have h1 : ‖w - z‖ < r := by simpa [dist_eq_norm] using hw
  have h2 : |(w - z).re| ≤ ‖w - z‖ := Complex.abs_re_le_norm _
  have h3 := (abs_lt.mp (h2.trans_lt h1)).1
  simp only [Complex.sub_re] at h3
  linarith

/- English proof (translation)
Introduce `ρ₀ h₀`. Assume the negation of the conclusion as `hρ₀`. Rewrite `hρ₀` using `[not_le]`. Take `⟨σ, hσ, C, hkey⟩` from `landau_window_key hP hθ hθ1 hδ hW`. Establish `hle : ∀ ρ ∈ Z, ρ.re < σ` using `fun ρ hρ => (landau_pole_re_le hP ρ hρ).trans_lt hσ`.

Break down `landau_dichotomy hP.iso hle hθ (by linarith) h₀ hρ₀ with ⟨D, hD, hfree, ρ₁, h₁, hρ₁⟩ | ⟨β, hβZ, hβ, r, hr1, hr2, huniq⟩` into its components or cases. Take `⟨γ, ρ, hρ, r, hr1, hr2, huniq⟩` from `landau_nearest hP.iso hle (by linarith : D < σ) h₁ hρ₁`. Take `⟨c, hc, -, hp⟩` from `hP.pole ρ hρ`. Use `set z : ℂ := (σ : ℂ) + γ * I with hz`. Establish `hzre : z.re = σ` using `by simp [hz]`.

Establish `hne : ρ ≠ z`. Introduce `h`. Use `hle ρ hρ` as an intermediate fact. Rewrite `this` using `[h, hzre]`. Conclude with `lt_irrefl _ this`.

Establish `hd : 0 < ‖z - ρ‖` using `norm_pos_iff.2 (sub_ne_zero.2 hne.symm)`. Use `set d := ‖z - ρ‖ with hddef`. Establish `hball : ρ ∈ Metric.ball z r`. Rewrite using `[Metric.mem_ball, dist_comm, dist_eq_norm]`. Conclude with `hr1`.

Establish `hdiff : DifferentiableOn ℂ Φ (Metric.ball z r \ {ρ})`. Use `hP.diff.mono ?_` and prove the remaining obligations. Introduce and unpack `w ⟨hw, hw'⟩`. Conclude with `⟨landau_window_re_pos (by rw [hzre]; linarith) hw, fun hZ => hw' (huniq w hZ hw)⟩`. Establish `hdiff' : DifferentiableOn ℂ Φ (Metric.ball (σ : ℂ) D)`.

Use `hP.diff.mono ?_` and prove the remaining obligations. Introduce `w hw`. Conclude with `⟨landau_window_re_pos (by rw [Complex.ofReal_re]; linarith) hw, fun hZ => hfree w hZ hw⟩`. Take `⟨M, hM⟩` from `landau_pole_asym (r' := (d + r) / 2) hball hne hdiff hp (by linarith) (by linarith)`. Take `⟨M', hM'⟩` from `landau_cauchy (r' := (d + r) / 2) hdiff' (by linarith) (by linarith)`.

Use `landau_window_contra (c := ‖c‖ / d) (d := d) (e := (d + r) / 2) (E := σ - θ) (M := M + M') (C := C) (div_pos (norm_pos_iff.2 hc) hd) hd (by linarith) (by linarith) fun η hη U₀ => ?_` and prove the remaining obligations. Take `⟨U, hU, k, hk, hb⟩` from `hkey η hη U₀`. Use `⟨U, hU, k, hk, ?_⟩` and prove the remaining obligations. Establish `h1` using `hb γ`. Establish `h2` using `hM k`.

Establish `h3` using `hM' k`. Establish `h4 : ‖c / (z - ρ) ^ (k + 1)‖ = ‖c‖ / d / d ^ k`. Rewrite using `[norm_div, norm_pow, pow_succ', div_div]`. Establish `h5 : ‖(-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)‖ = ‖iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)‖`. Rewrite using `[mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]`.

Establish `h6` using `(abs_le.mp (Complex.abs_re_le_norm ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)))).1`. Establish `h7` using `norm_sub_norm_le (c / (z - ρ) ^ (k + 1)) ((-1) ^ k * iteratedDeriv k Φ z / (k.factorial : ℂ))`. Rewrite `h7` using `[norm_sub_rev]`. Rewrite using `[add_div]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨c, -, hc, hp⟩` from `hP.pole β hβZ`. Take `⟨hc1, hc2⟩` from `hc (Complex.ofReal_im β)`. Establish `hd : 0 < σ - β`. Use `hle β hβZ` as an intermediate fact. Rewrite `this` using `[Complex.ofReal_re]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hne : (β : ℂ) ≠ (σ : ℂ)`. Introduce `h`. Establish `: β = σ` using `by exact_mod_cast h`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hball : (β : ℂ) ∈ Metric.ball (σ : ℂ) r`. Rewrite using `[Metric.mem_ball, dist_comm, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]`. Conclude with `hr1`. Establish `hdiff : DifferentiableOn ℂ Φ (Metric.ball (σ : ℂ) r \ {(β : ℂ)})`. Use `hP.diff.mono ?_` and prove the remaining obligations.

Introduce and unpack `w ⟨hw, hw'⟩`. Conclude with `⟨landau_window_re_pos (by rw [Complex.ofReal_re]; linarith) hw, fun hZ => hw' (huniq w hZ hw)⟩`. Take `⟨M, hM⟩` from `landau_pole_asym (r' := (σ - β + r) / 2) hball hne hdiff hp (by linarith) (by linarith)`. Use `landau_window_contra (c := c.re / (σ - β)) (d := σ - β) (e := (σ - β + r) / 2) (E := σ - θ) (M := M) (C := C) (div_pos hc1 hd) hd (by linarith) (by linarith) fun η hη U₀ => ?_` and prove the remaining obligations. Take `⟨U, hU, k, hk, hb⟩` from `hkey η hη U₀`.

Use `⟨U, hU, k, hk, ?_⟩` and prove the remaining obligations. Establish `h1` using `hb 0`. Establish `h2` using `hM k`. Establish `h4 : (c / ((σ : ℂ) - β) ^ (k + 1)).re = c.re / (σ - β) / (σ - β) ^ k`. Rewrite using `[← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.div_ofReal_re, pow_succ', div_div]`.

Establish `h6` using `(abs_le.mp (Complex.abs_re_le_norm ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ) - c / ((σ : ℂ) - β) ^ (k + 1)))).1`. Rewrite `h6` using `[Complex.sub_re, h4]`. Establish `h7` using `norm_nonneg ((-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + (0 : ℝ) * I) / (k.factorial : ℂ))`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem landau_window {g : ℝ → ℝ} {Φ : ℂ → ℂ} {Z : Set ℂ} (hP : PoleData g Φ Z) {θ δ : ℝ}
    (hθ : 0 < θ) (hθ1 : θ < 1) (hδ : 0 < δ) (hW : WindowHypU g θ δ) : ∀ ρ ∈ Z, ρ.re ≤ θ := by
  intro ρ₀ h₀
  by_contra hρ₀
  rw [not_le] at hρ₀
  obtain ⟨σ, hσ, C, hkey⟩ := landau_window_key hP hθ hθ1 hδ hW
  have hle : ∀ ρ ∈ Z, ρ.re < σ := fun ρ hρ => (landau_pole_re_le hP ρ hρ).trans_lt hσ
  rcases landau_dichotomy hP.iso hle hθ (by linarith) h₀ hρ₀ with
    ⟨D, hD, hfree, ρ₁, h₁, hρ₁⟩ | ⟨β, hβZ, hβ, r, hr1, hr2, huniq⟩
  · obtain ⟨γ, ρ, hρ, r, hr1, hr2, huniq⟩ := landau_nearest hP.iso hle (by linarith : D < σ) h₁ hρ₁
    obtain ⟨c, hc, -, hp⟩ := hP.pole ρ hρ
    set z : ℂ := (σ : ℂ) + γ * I with hz
    have hzre : z.re = σ := by simp [hz]
    have hne : ρ ≠ z := by
      intro h
      have := hle ρ hρ
      rw [h, hzre] at this
      exact lt_irrefl _ this
    have hd : 0 < ‖z - ρ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne.symm)
    set d := ‖z - ρ‖ with hddef
    have hball : ρ ∈ Metric.ball z r := by
      rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact hr1
    have hdiff : DifferentiableOn ℂ Φ (Metric.ball z r \ {ρ}) := by
      refine hP.diff.mono ?_
      rintro w ⟨hw, hw'⟩
      exact ⟨landau_window_re_pos (by rw [hzre]; linarith) hw, fun hZ => hw' (huniq w hZ hw)⟩
    have hdiff' : DifferentiableOn ℂ Φ (Metric.ball (σ : ℂ) D) := by
      refine hP.diff.mono ?_
      intro w hw
      exact ⟨landau_window_re_pos (by rw [Complex.ofReal_re]; linarith) hw, fun hZ => hfree w hZ hw⟩
    obtain ⟨M, hM⟩ := landau_pole_asym (r' := (d + r) / 2) hball hne hdiff hp (by linarith) (by linarith)
    obtain ⟨M', hM'⟩ := landau_cauchy (r' := (d + r) / 2) hdiff' (by linarith) (by linarith)
    refine landau_window_contra (c := ‖c‖ / d) (d := d) (e := (d + r) / 2) (E := σ - θ) (M := M + M') (C := C)
      (div_pos (norm_pos_iff.2 hc) hd) hd (by linarith) (by linarith) fun η hη U₀ => ?_
    obtain ⟨U, hU, k, hk, hb⟩ := hkey η hη U₀
    refine ⟨U, hU, k, hk, ?_⟩
    have h1 := hb γ
    have h2 := hM k
    have h3 := hM' k
    have h4 : ‖c / (z - ρ) ^ (k + 1)‖ = ‖c‖ / d / d ^ k := by
      rw [norm_div, norm_pow, pow_succ', div_div]
    have h5 : ‖(-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)‖
        = ‖iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)‖ := by
      rw [mul_div_assoc, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have h6 := (abs_le.mp (Complex.abs_re_le_norm
      ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ)))).1
    have h7 := norm_sub_norm_le (c / (z - ρ) ^ (k + 1))
      ((-1) ^ k * iteratedDeriv k Φ z / (k.factorial : ℂ))
    rw [norm_sub_rev] at h7
    rw [add_div]
    linarith
  · obtain ⟨c, -, hc, hp⟩ := hP.pole β hβZ
    obtain ⟨hc1, hc2⟩ := hc (Complex.ofReal_im β)
    have hd : 0 < σ - β := by
      have := hle β hβZ
      rw [Complex.ofReal_re] at this
      linarith
    have hne : (β : ℂ) ≠ (σ : ℂ) := by
      intro h
      have : β = σ := by exact_mod_cast h
      linarith
    have hball : (β : ℂ) ∈ Metric.ball (σ : ℂ) r := by
      rw [Metric.mem_ball, dist_comm, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hd]
      exact hr1
    have hdiff : DifferentiableOn ℂ Φ (Metric.ball (σ : ℂ) r \ {(β : ℂ)}) := by
      refine hP.diff.mono ?_
      rintro w ⟨hw, hw'⟩
      exact ⟨landau_window_re_pos (by rw [Complex.ofReal_re]; linarith) hw,
        fun hZ => hw' (huniq w hZ hw)⟩
    obtain ⟨M, hM⟩ := landau_pole_asym (r' := (σ - β + r) / 2) hball hne hdiff hp (by linarith) (by linarith)
    refine landau_window_contra (c := c.re / (σ - β)) (d := σ - β) (e := (σ - β + r) / 2) (E := σ - θ)
      (M := M) (C := C) (div_pos hc1 hd) hd (by linarith) (by linarith) fun η hη U₀ => ?_
    obtain ⟨U, hU, k, hk, hb⟩ := hkey η hη U₀
    refine ⟨U, hU, k, hk, ?_⟩
    have h1 := hb 0
    have h2 := hM k
    have h4 : (c / ((σ : ℂ) - β) ^ (k + 1)).re = c.re / (σ - β) / (σ - β) ^ k := by
      rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.div_ofReal_re, pow_succ', div_div]
    have h6 := (abs_le.mp (Complex.abs_re_le_norm
      ((-1) ^ k * iteratedDeriv k Φ (σ : ℂ) / (k.factorial : ℂ) - c / ((σ : ℂ) - β) ^ (k + 1)))).1
    rw [Complex.sub_re, h4] at h6
    have h7 := norm_nonneg ((-1) ^ k * iteratedDeriv k Φ ((σ : ℂ) + (0 : ℝ) * I) / (k.factorial : ℂ))
    linarith

end Deduction

end
