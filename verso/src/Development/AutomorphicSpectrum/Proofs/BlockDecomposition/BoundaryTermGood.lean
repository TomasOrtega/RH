import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold

noncomputable section

open MeasureTheory Filter Topology Metric PositivityTheory.RgEis PositivityTheory.RgEis.MG

namespace GlobalTheory.CompanionTheory.RgEisLeft

/- English proof (translation)
Use `set X := max |b| |c| with hX`. Establish `hX0 : 0 ≤ X` using `le_trans (abs_nonneg _) (le_max_left _ _)`. Use `⟨8 * Real.exp ((1 + X) ^ 2 + X ^ 2), by positivity, fun z hb hc => ?_⟩` and prove the remaining obligations. Establish `hx : |z.re| ≤ X`. Rewrite using `[abs_le]`.

Prove the components needed by the constructor for the conclusion. Establish `h1` using `neg_abs_le b`. Establish `h2` using `le_max_left |b| |c|`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `le_abs_self c`.

Establish `h2` using `le_max_right |b| |c|`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn : ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2 - z.im ^ 2)`. Rewrite using `[Complex.norm_exp]`. Use `congr 1`.

Simplify using `[pow_two, Complex.mul_re]`. Establish `hz : ‖z‖ ≤ |z.re| + |z.im|` using `Complex.norm_le_abs_re_add_abs_im z`. Take `⟨t, ht⟩ : ∃ t, t = 1 + ‖z‖` from `⟨_, rfl⟩`. Rewrite using `[← ht, hn]`. Establish `ht0 : 0 ≤ t` using `by rw [ht]; positivity`.

Establish `hta : t ≤ (1 + X) + |z.im|` using `by linarith`. Establish `ht2 : t ^ 2 ≤ 2 * (1 + X) ^ 2 + 2 * z.im ^ 2`. Establish `h1 : t ^ 2 ≤ ((1 + X) + |z.im|) ^ 2` using `pow_le_pow_left₀ ht0 hta 2`. Establish `h2 : |z.im| ^ 2 = z.im ^ 2` using `sq_abs _`. Use polynomial arithmetic with `[sq_nonneg ((1 + X) - |z.im|)]`.

Establish `h4 : t ^ 4 ≤ 8 * Real.exp (t ^ 2 / 2)`. Establish `h1` using `Real.quadratic_le_exp_of_nonneg (x := t ^ 2 / 2) (by positivity)`. Establish `h2 : t ^ 4 = 8 * ((t ^ 2 / 2) ^ 2 / 2)` using `by ring`. Establish `h3 : 0 ≤ t ^ 2 / 2` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hx2 : z.re ^ 2 ≤ X ^ 2`. Rewrite using `[← sq_abs z.re]`. Conclude with `pow_le_pow_left₀ (abs_nonneg _) hx 2`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma gauss_strip (b c : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
    ‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 4 ≤ C := by
  set X := max |b| |c| with hX
  have hX0 : 0 ≤ X := le_trans (abs_nonneg _) (le_max_left _ _)
  refine ⟨8 * Real.exp ((1 + X) ^ 2 + X ^ 2), by positivity, fun z hb hc => ?_⟩
  have hx : |z.re| ≤ X := by
    rw [abs_le]
    constructor
    · have h1 := neg_abs_le b
      have h2 := le_max_left |b| |c|
      linarith
    · have h1 := le_abs_self c
      have h2 := le_max_right |b| |c|
      linarith
  have hn : ‖Complex.exp (z ^ 2)‖ = Real.exp (z.re ^ 2 - z.im ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [pow_two, Complex.mul_re]
  have hz : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  obtain ⟨t, ht⟩ : ∃ t, t = 1 + ‖z‖ := ⟨_, rfl⟩
  rw [← ht, hn]
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  have hta : t ≤ (1 + X) + |z.im| := by linarith
  have ht2 : t ^ 2 ≤ 2 * (1 + X) ^ 2 + 2 * z.im ^ 2 := by
    have h1 : t ^ 2 ≤ ((1 + X) + |z.im|) ^ 2 := pow_le_pow_left₀ ht0 hta 2
    have h2 : |z.im| ^ 2 = z.im ^ 2 := sq_abs _
    nlinarith [sq_nonneg ((1 + X) - |z.im|)]
  have h4 : t ^ 4 ≤ 8 * Real.exp (t ^ 2 / 2) := by
    have h1 := Real.quadratic_le_exp_of_nonneg (x := t ^ 2 / 2) (by positivity)
    have h2 : t ^ 4 = 8 * ((t ^ 2 / 2) ^ 2 / 2) := by ring
    have h3 : 0 ≤ t ^ 2 / 2 := by positivity
    linarith
  have hx2 : z.re ^ 2 ≤ X ^ 2 := by
    rw [← sq_abs z.re]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  calc Real.exp (z.re ^ 2 - z.im ^ 2) * t ^ 4
      ≤ Real.exp (z.re ^ 2 - z.im ^ 2) * (8 * Real.exp (t ^ 2 / 2)) := by gcongr
    _ = 8 * Real.exp (z.re ^ 2 - z.im ^ 2 + t ^ 2 / 2) := by rw [Real.exp_add]; ring
    _ ≤ 8 * Real.exp ((1 + X) ^ 2 + X ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)

/- English proof (translation)
Establish `hd1 : DifferentiableOn ℂ (fun z => (Complex.exp (z ^ 2) * (z - 1)) • A z) {z | z.re < 1 / 2}` using `DifferentiableOn.smul (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.exp (z ^ 2) * (z - 1)).differentiableOn hd`. Establish `hd2 : DifferentiableOn ℂ (fun z => z • (Complex.exp (z ^ 2) * (z - 1)) • A z) {z | z.re < 1 / 2}` using `DifferentiableOn.smul differentiableOn_id hd1`. Establish `key : ∀ b c : ℝ, c < 1 / 2 → ∃ B : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c → ‖(Complex.exp (z ^ 2) * (z - 1)) • A z‖ * (1 + ‖z‖) ≤ B`. Introduce `b c hc`. Take `⟨M, hM⟩` from `hb b c hc`.

Take `⟨C, hC0, hC⟩` from `gauss_strip b c`. Use `⟨|M| * C, fun z h1 h2 => ?_⟩` and prove the remaining obligations. Establish `hA : ‖A z‖ ≤ |M| * (1 + ‖z‖) ^ 2` using `(hM z h1 h2).trans (by gcongr; exact le_abs_self M)`. Establish `hz1 : ‖z - 1‖ ≤ 1 + ‖z‖`. Use `norm_sub_le z 1` as an intermediate fact.

Simplify using `only [norm_one] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ht : 0 ≤ 1 + ‖z‖` using `by positivity`. Rewrite using `[norm_smul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hC z h1 h2`. Use `⟨⟨hd1, fun b c hc => ?_⟩, ⟨hd2, fun b c hc => ?_⟩⟩` and prove the remaining obligations. Take `⟨B, hB⟩` from `key b c hc`. Use `⟨B, fun z h1 h2 => le_trans ?_ (hB z h1 h2)⟩` and prove the remaining obligations. Establish `: 1 ≤ 1 + ‖z‖` using `by simp`.

Conclude with `le_mul_of_one_le_right (norm_nonneg _) this`. Take `⟨B, hB⟩` from `key b c hc`. Use `⟨B, fun z h1 h2 => le_trans ?_ (hB z h1 h2)⟩` and prove the remaining obligations. Rewrite using `[norm_smul, mul_comm]`. Establish `: ‖z‖ ≤ 1 + ‖z‖` using `by simp`.

Use `gcongr`.
-/
lemma leftGood_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A : ℂ → E}
    (hd : DifferentiableOn ℂ A {z | z.re < 1 / 2})
    (hb : ∀ b c : ℝ, c < 1 / 2 → ∃ M : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c → ‖A z‖ ≤ M * (1 + ‖z‖) ^ 2) :
    LeftGood (fun z => (Complex.exp (z ^ 2) * (z - 1)) • A z) (1 / 2) ∧
    LeftGood (fun z => z • (Complex.exp (z ^ 2) * (z - 1)) • A z) (1 / 2) := by
  have hd1 : DifferentiableOn ℂ (fun z => (Complex.exp (z ^ 2) * (z - 1)) • A z) {z | z.re < 1 / 2} :=
    DifferentiableOn.smul
      (by fun_prop : Differentiable ℂ fun z : ℂ => Complex.exp (z ^ 2) * (z - 1)).differentiableOn hd
  have hd2 : DifferentiableOn ℂ (fun z => z • (Complex.exp (z ^ 2) * (z - 1)) • A z) {z | z.re < 1 / 2} :=
    DifferentiableOn.smul differentiableOn_id hd1
  have key : ∀ b c : ℝ, c < 1 / 2 → ∃ B : ℝ, ∀ z : ℂ, b ≤ z.re → z.re ≤ c →
      ‖(Complex.exp (z ^ 2) * (z - 1)) • A z‖ * (1 + ‖z‖) ≤ B := by
    intro b c hc
    obtain ⟨M, hM⟩ := hb b c hc
    obtain ⟨C, hC0, hC⟩ := gauss_strip b c
    refine ⟨|M| * C, fun z h1 h2 => ?_⟩
    have hA : ‖A z‖ ≤ |M| * (1 + ‖z‖) ^ 2 :=
      (hM z h1 h2).trans (by gcongr; exact le_abs_self M)
    have hz1 : ‖z - 1‖ ≤ 1 + ‖z‖ := by
      have := norm_sub_le z 1
      simp only [norm_one] at this
      linarith
    have ht : 0 ≤ 1 + ‖z‖ := by positivity
    rw [norm_smul, norm_mul]
    calc ‖Complex.exp (z ^ 2)‖ * ‖z - 1‖ * ‖A z‖ * (1 + ‖z‖)
        ≤ ‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) * (|M| * (1 + ‖z‖) ^ 2) * (1 + ‖z‖) := by gcongr
      _ = |M| * (‖Complex.exp (z ^ 2)‖ * (1 + ‖z‖) ^ 4) := by ring
      _ ≤ |M| * C := by
          gcongr
          exact hC z h1 h2
  refine ⟨⟨hd1, fun b c hc => ?_⟩, ⟨hd2, fun b c hc => ?_⟩⟩
  · obtain ⟨B, hB⟩ := key b c hc
    refine ⟨B, fun z h1 h2 => le_trans ?_ (hB z h1 h2)⟩
    have : 1 ≤ 1 + ‖z‖ := by simp
    exact le_mul_of_one_le_right (norm_nonneg _) this
  · obtain ⟨B, hB⟩ := key b c hc
    refine ⟨B, fun z h1 h2 => le_trans ?_ (hB z h1 h2)⟩
    rw [norm_smul, mul_comm]
    have : ‖z‖ ≤ 1 + ‖z‖ := by simp
    gcongr

/- English proof (translation)
Establish `hopen : IsOpen {z : ℂ | z.re < 1 / 2}` using `isOpen_lt Complex.continuous_re continuous_const`. Introduce `z₀ hz₀`. Establish `hz₀' : z₀.re < 1 / 2` using `hz₀`. Take `⟨ε, hε⟩ : ∃ ε, ε = (1 / 2 - z₀.re) / 4` from `⟨_, rfl⟩`. Establish `hε0 : 0 < ε` using `by rw [hε]; linarith`.

Establish `hball : ∀ w ∈ closedBall z₀ (2 * ε), w.re < 1 / 2 ∧ z₀.re - 2 * ε ≤ w.re ∧ w.re ≤ z₀.re + 2 * ε ∧ ‖w‖ ≤ ‖z₀‖ + 2 * ε`. Introduce `w hw`. Establish `h1 : ‖w - z₀‖ ≤ 2 * ε` using `by simpa [dist_eq_norm] using hw`. Establish `h2 : |(w - z₀).re| ≤ ‖w - z₀‖` using `Complex.abs_re_le_norm _`. Establish `h3` using `abs_le.mp (h2.trans h1)`.

Establish `h4 : ‖w‖ ≤ ‖z₀‖ + ‖w - z₀‖`. Use `norm_add_le z₀ (w - z₀)` as an intermediate fact. Simplify using `using this`. Simplify using `only [Complex.sub_re] at h3`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith`.

Establish `hsub : closedBall z₀ (2 * ε) ⊆ {z : ℂ | z.re < 1 / 2}` using `fun w hw => (hball w hw).1`. Take `⟨M, hM⟩` from `hζ.strip (z₀.re - 2 * ε) (z₀.re + 2 * ε) (by rw [hε]; linarith)`. Take `⟨B, hB⟩ : ∃ B : ℝ, B = |M| * (1 + (‖z₀‖ + 2 * ε)) ^ 2` from `⟨_, rfl⟩`. Establish `hbd : ∀ w ∈ closedBall z₀ (2 * ε), ∀ t, ‖ζ w t‖ ≤ B`. Introduce `w hw t`.

Take `⟨-, h2, h3, h4⟩` from `hball w hw`. Use `(hM w h2 h3 t).trans ?_` and prove the remaining obligations. Rewrite using `[hB]`. Use `gcongr`. Conclude with `le_abs_self M`.

Take `⟨R, hR⟩` from `isCompact_univ.exists_bound_of_continuousOn hr.continuousOn`. Establish `hR' : ∀ t, ‖r t‖ ≤ R` using `fun t => hR t (Set.mem_univ t)`. Establish `hcont : ∀ z : ℂ, z.re < 1 / 2 → Continuous (ζ z)`. Introduce `z hz`. Establish `h` using `hζ.cont.comp_continuous (f := fun t : T => (z, t)) (by fun_prop) (fun t => ⟨hz, Set.mem_univ t⟩)`.

Conclude with `h`. Establish `hmeasF : ∀ z : ℂ, z.re < 1 / 2 → AEStronglyMeasurable (fun κ => ζ z κ • r κ) μ` using `fun z hz => ((hcont z hz).measurable.aestronglyMeasurable).smul hr.aestronglyMeasurable`. Establish `hdiff : ∀ (t : T) (z : ℂ), z.re < 1 / 2 → HasDerivAt (ζ · t) (deriv (ζ · t) z) z` using `fun t z hz => (((hζ.hol t) z hz).differentiableAt (hopen.mem_nhds hz)).hasDerivAt`. Establish `hd0 : Measurable fun t => deriv (ζ · t) z₀`. Set `h : ℕ → ℂ` to `fun n => ((ε / (n + 1) : ℝ) : ℂ)`.

Establish `hh0 : ∀ n, h n ≠ 0` using `fun n => by`. Establish `: ε / ((n : ℝ) + 1) ≠ 0` using `by positivity`. Conclude with `Complex.ofReal_ne_zero.mpr this`. Establish `hhs : ∀ n, z₀ + h n ∈ closedBall z₀ (2 * ε)`. Introduce `n`.

Establish `h1 : ε / ((n : ℝ) + 1) ≤ ε` using `div_le_self hε0.le (by simp)`. Establish `h2 : 0 ≤ ε / ((n : ℝ) + 1)` using `by positivity`. Simplify using `only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlim : Tendsto h atTop (𝓝[≠] 0)`.

Use `tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hh0⟩` and prove the remaining obligations. Establish `h1 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 1)) atTop (𝓝 0)`. Establish `h0` using `(tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε`. Simplify `h0` using `[div_eq_mul_inv]`. Establish `h2` using `(Complex.continuous_ofReal.tendsto 0).comp h1`.

Simplify `h2` using `[h, Function.comp_def]`. Use `measurable_of_tendsto_metrizable (f := fun (n : ℕ) t => (h n)⁻¹ • (ζ (z₀ + h n) t - ζ z₀ t)) (fun n => ?_) ?_` and prove the remaining obligations. Establish `hc : Continuous fun t => (h n)⁻¹ • (ζ (z₀ + h n) t - ζ z₀ t)` using `(continuous_const_smul (h n)⁻¹).comp (show Continuous fun t => ζ (z₀ + h n) t - ζ z₀ t from (hcont _ (hsub (hhs n))).sub (hcont _ hz₀'))`. Conclude with `hc.measurable`. Rewrite using `[tendsto_pi_nhds]`.

Introduce `t`. Conclude with `(hasDerivAt_iff_tendsto_slope_zero.mp (hdiff t z₀ hz₀')).comp hlim`. Establish `hmain` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℂ) (F := fun z κ => ζ z κ • r κ) (F' := fun z κ => deriv (ζ · κ) z • r κ) (x₀ := z₀) (s := ball z₀ ε) (bound := fun _ => B / ε * R) (ball_mem_nhds z₀ hε0) (by filter_upwards [hopen.mem_nhds hz₀] with z hz using hmeas …`. Use `Integrable.of_bound (hmeasF z₀ hz₀') (B * R) (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul]`.

Establish `h1` using `hbd z₀ (mem_closedBall_self (by positivity)) t`. Establish `h0 : 0 ≤ B` using `(norm_nonneg _).trans h1`. Conclude with `mul_le_mul h1 (hR' t) (norm_nonneg _) h0)`. Use the proof step `(hd0.aestronglyMeasurable.smul hr.aestronglyMeasurable)`. Use the proof step `(Eventually.of_forall fun t z hz => by`.

Establish `hz' : dist z z₀ < ε` using `hz`. Establish `hsph : closedBall z ε ⊆ closedBall z₀ (2 * ε)`. Introduce `w hw`. Establish `h1 : dist w z ≤ ε` using `hw`. Establish `h2` using `dist_triangle w z z₀`.

Use `show dist w z₀ ≤ 2 * ε`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hder : ‖deriv (ζ · t) z‖ ≤ B / ε` using `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε0 (((hζ.hol t).mono hsub).mono hsph |>.diffContOnCl_ball subset_rfl) (fun w hw => hbd w (hsph (sphere_subset_closedBall hw)) t)`. Rewrite using `[norm_smul]`. Conclude with `mul_le_mul hder (hR' t) (norm_nonneg _) ((norm_nonneg _).trans hder))`.

Use the proof step `(integrable_const _)`. Use the proof step `(Eventually.of_forall fun t z hz => by`. Establish `hz' : z ∈ closedBall z₀ (2 * ε)`. Establish `: dist z z₀ < ε` using `hz`. Use `show dist z z₀ ≤ 2 * ε`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(hdiff t z (hsub hz')).smul_const (r t))`. Conclude with `hmain.2.differentiableAt.differentiableWithinAt`.
-/
theorem differentiableOn_integral {T E : Type} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T]
    [BorelSpace T] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [SecondCountableTopology E] (μ : Measure T) [IsFiniteMeasure μ] {r : T → E} (hr : Continuous r)
    {ζ : ℂ → T → ℂ} (hζ : LeftFam ζ) :
    DifferentiableOn ℂ (fun z => ∫ κ, ζ z κ • r κ ∂μ) {z | z.re < 1 / 2} := by
  have hopen : IsOpen {z : ℂ | z.re < 1 / 2} := isOpen_lt Complex.continuous_re continuous_const
  intro z₀ hz₀
  have hz₀' : z₀.re < 1 / 2 := hz₀
  obtain ⟨ε, hε⟩ : ∃ ε, ε = (1 / 2 - z₀.re) / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hball : ∀ w ∈ closedBall z₀ (2 * ε), w.re < 1 / 2 ∧ z₀.re - 2 * ε ≤ w.re ∧ w.re ≤ z₀.re + 2 * ε ∧
      ‖w‖ ≤ ‖z₀‖ + 2 * ε := by
    intro w hw
    have h1 : ‖w - z₀‖ ≤ 2 * ε := by simpa [dist_eq_norm] using hw
    have h2 : |(w - z₀).re| ≤ ‖w - z₀‖ := Complex.abs_re_le_norm _
    have h3 := abs_le.mp (h2.trans h1)
    have h4 : ‖w‖ ≤ ‖z₀‖ + ‖w - z₀‖ := by
      have := norm_add_le z₀ (w - z₀)
      simpa using this
    simp only [Complex.sub_re] at h3
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith
  have hsub : closedBall z₀ (2 * ε) ⊆ {z : ℂ | z.re < 1 / 2} := fun w hw => (hball w hw).1
  obtain ⟨M, hM⟩ := hζ.strip (z₀.re - 2 * ε) (z₀.re + 2 * ε) (by rw [hε]; linarith)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = |M| * (1 + (‖z₀‖ + 2 * ε)) ^ 2 := ⟨_, rfl⟩
  have hbd : ∀ w ∈ closedBall z₀ (2 * ε), ∀ t, ‖ζ w t‖ ≤ B := by
    intro w hw t
    obtain ⟨-, h2, h3, h4⟩ := hball w hw
    refine (hM w h2 h3 t).trans ?_
    rw [hB]
    gcongr
    exact le_abs_self M
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn hr.continuousOn
  have hR' : ∀ t, ‖r t‖ ≤ R := fun t => hR t (Set.mem_univ t)
  have hcont : ∀ z : ℂ, z.re < 1 / 2 → Continuous (ζ z) := by
    intro z hz
    have h := hζ.cont.comp_continuous (f := fun t : T => (z, t)) (by fun_prop)
      (fun t => ⟨hz, Set.mem_univ t⟩)
    exact h
  have hmeasF : ∀ z : ℂ, z.re < 1 / 2 → AEStronglyMeasurable (fun κ => ζ z κ • r κ) μ := fun z hz =>
    ((hcont z hz).measurable.aestronglyMeasurable).smul hr.aestronglyMeasurable
  have hdiff : ∀ (t : T) (z : ℂ), z.re < 1 / 2 → HasDerivAt (ζ · t) (deriv (ζ · t) z) z := fun t z hz =>
    (((hζ.hol t) z hz).differentiableAt (hopen.mem_nhds hz)).hasDerivAt
  have hd0 : Measurable fun t => deriv (ζ · t) z₀ := by
    let h : ℕ → ℂ := fun n => ((ε / (n + 1) : ℝ) : ℂ)
    have hh0 : ∀ n, h n ≠ 0 := fun n => by
      have : ε / ((n : ℝ) + 1) ≠ 0 := by positivity
      exact Complex.ofReal_ne_zero.mpr this
    have hhs : ∀ n, z₀ + h n ∈ closedBall z₀ (2 * ε) := by
      intro n
      have h1 : ε / ((n : ℝ) + 1) ≤ ε := div_le_self hε0.le (by simp)
      have h2 : 0 ≤ ε / ((n : ℝ) + 1) := by positivity
      simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, h, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg h2]
      linarith
    have hlim : Tendsto h atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall hh0⟩
      have h1 : Tendsto (fun n : ℕ => ε / ((n : ℝ) + 1)) atTop (𝓝 0) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
        simpa [div_eq_mul_inv] using h0
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa [h, Function.comp_def] using h2
    refine measurable_of_tendsto_metrizable
      (f := fun (n : ℕ) t => (h n)⁻¹ • (ζ (z₀ + h n) t - ζ z₀ t)) (fun n => ?_) ?_
    · have hc : Continuous fun t => (h n)⁻¹ • (ζ (z₀ + h n) t - ζ z₀ t) :=
        (continuous_const_smul (h n)⁻¹).comp
          (show Continuous fun t => ζ (z₀ + h n) t - ζ z₀ t from
            (hcont _ (hsub (hhs n))).sub (hcont _ hz₀'))
      exact hc.measurable
    · rw [tendsto_pi_nhds]
      intro t
      exact (hasDerivAt_iff_tendsto_slope_zero.mp (hdiff t z₀ hz₀')).comp hlim
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℂ)
    (F := fun z κ => ζ z κ • r κ) (F' := fun z κ => deriv (ζ · κ) z • r κ) (x₀ := z₀)
    (s := ball z₀ ε) (bound := fun _ => B / ε * R)
    (ball_mem_nhds z₀ hε0)
    (by
      filter_upwards [hopen.mem_nhds hz₀] with z hz using hmeasF z hz)
    (by
      refine Integrable.of_bound (hmeasF z₀ hz₀') (B * R) (Eventually.of_forall fun t => ?_)
      rw [norm_smul]
      have h1 := hbd z₀ (mem_closedBall_self (by positivity)) t
      have h0 : 0 ≤ B := (norm_nonneg _).trans h1
      exact mul_le_mul h1 (hR' t) (norm_nonneg _) h0)
    (hd0.aestronglyMeasurable.smul hr.aestronglyMeasurable)
    (Eventually.of_forall fun t z hz => by
      have hz' : dist z z₀ < ε := hz
      have hsph : closedBall z ε ⊆ closedBall z₀ (2 * ε) := by
        intro w hw
        have h1 : dist w z ≤ ε := hw
        have h2 := dist_triangle w z z₀
        show dist w z₀ ≤ 2 * ε
        linarith
      have hder : ‖deriv (ζ · t) z‖ ≤ B / ε :=
        Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hε0
          (((hζ.hol t).mono hsub).mono hsph |>.diffContOnCl_ball subset_rfl)
          (fun w hw => hbd w (hsph (sphere_subset_closedBall hw)) t)
      rw [norm_smul]
      exact mul_le_mul hder (hR' t) (norm_nonneg _) ((norm_nonneg _).trans hder))
    (integrable_const _)
    (Eventually.of_forall fun t z hz => by
      have hz' : z ∈ closedBall z₀ (2 * ε) := by
        have : dist z z₀ < ε := hz
        show dist z z₀ ≤ 2 * ε
        linarith
      exact (hdiff t z (hsub hz')).smul_const (r t))
  exact hmain.2.differentiableAt.differentiableWithinAt

/- English proof (translation)
Introduce `G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hH hP ζ hζ`. Use `haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK`. Use `haveI : CompleteSpace W := FiniteDimensional.complete ℂ W`. Use `haveI : ProperSpace (W →L[ℂ] W) := FiniteDimensional.proper ℂ _`. Use `haveI : IsProbabilityMeasure μ := hP`.

Take `⟨R, hR⟩` from `(isCompact_univ (X := K)).exists_bound_of_continuousOn hρ.continuousOn`. Use `leftGood_of (A := fun z => avg μ ρ (ζ z)) (differentiableOn_integral μ hρ hζ) ?_` and prove the remaining obligations. Introduce `b c hc`. Take `⟨M, hM⟩` from `hζ.strip b c hc`. Use `⟨|M| * |R|, fun z h1 h2 => ?_⟩` and prove the remaining obligations.

Establish `hpt : ∀ κ : K, ‖ζ z κ • ρ κ‖ ≤ |M| * |R| * (1 + ‖z‖) ^ 2`. Introduce `κ`. Rewrite using `[norm_smul]`. Establish `h3 : ‖ζ z κ‖ ≤ |M| * (1 + ‖z‖) ^ 2` using `(hM z h1 h2 κ).trans (by gcongr; exact le_abs_self M)`. Establish `h4 : ‖ρ κ‖ ≤ |R|` using `(hR κ (Set.mem_univ κ)).trans (le_abs_self R)`.

Combine the equalities or inequalities in the displayed calculation. Use `norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpt)` as an intermediate fact. Simplify `this` using `[avg]`.
-/
theorem bGood : BGood := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ _ _ μ hH hP ζ hζ
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  haveI : ProperSpace (W →L[ℂ] W) := FiniteDimensional.proper ℂ _
  haveI : IsProbabilityMeasure μ := hP
  obtain ⟨R, hR⟩ := (isCompact_univ (X := K)).exists_bound_of_continuousOn hρ.continuousOn
  refine leftGood_of (A := fun z => avg μ ρ (ζ z)) (differentiableOn_integral μ hρ hζ) ?_
  intro b c hc
  obtain ⟨M, hM⟩ := hζ.strip b c hc
  refine ⟨|M| * |R|, fun z h1 h2 => ?_⟩
  have hpt : ∀ κ : K, ‖ζ z κ • ρ κ‖ ≤ |M| * |R| * (1 + ‖z‖) ^ 2 := by
    intro κ
    rw [norm_smul]
    have h3 : ‖ζ z κ‖ ≤ |M| * (1 + ‖z‖) ^ 2 :=
      (hM z h1 h2 κ).trans (by gcongr; exact le_abs_self M)
    have h4 : ‖ρ κ‖ ≤ |R| := (hR κ (Set.mem_univ κ)).trans (le_abs_self R)
    calc ‖ζ z κ‖ * ‖ρ κ‖ ≤ (|M| * (1 + ‖z‖) ^ 2) * |R| :=
          mul_le_mul h3 h4 (norm_nonneg _) (by positivity)
      _ = |M| * |R| * (1 + ‖z‖) ^ 2 := by ring
  have := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpt)
  simpa [avg] using this

end GlobalTheory.CompanionTheory.RgEisLeft
