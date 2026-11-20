import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExponentialFourierIntegralBound

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier.InvLine

/- English proof (translation)
The claim follows from `(integrable_exp_neg_mul_abs hc).mul_prod (integrable_exp_neg_mul_abs hc)`.
-/
theorem integrable_exp_neg_abs_plane {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ × ℝ => Real.exp (-c * |t.1|) * Real.exp (-c * |t.2|)) :=
  (integrable_exp_neg_mul_abs hc).mul_prod (integrable_exp_neg_mul_abs hc)

/- English proof (translation)
Simplify using `[dot]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dot_add_smul (p v : ℂ × ℂ) (τ : ℂ) (t : ℝ × ℝ) :
    dot (p + τ • v) t = dot p t + τ * dot v t := by
  simp [dot]
  ring

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Simplify using `[dot, rdot]`.
-/
theorem norm_cexp_dot (l : ℂ × ℂ) (t : ℝ × ℝ) :
    ‖Complex.exp (dot l t)‖ = Real.exp (rdot (l.1.re, l.2.re) t) := by
  rw [Complex.norm_exp]
  simp [dot, rdot]

/- English proof (translation)
Establish `h1 : ‖dot v t‖ ≤ ‖v.1‖ * |t.1| + ‖v.2‖ * |t.2|`. Use `(norm_add_le _ _).trans ?_` and prove the remaining obligations. Simplify using `[norm_mul]`. Use `norm_nonneg v.1` as an intermediate fact. Use `norm_nonneg v.2` as an intermediate fact.

Use `abs_nonneg t.1` as an intermediate fact. Use `abs_nonneg t.2` as an intermediate fact. Use polynomial arithmetic with `[mul_nonneg (norm_nonneg v.1) (abs_nonneg t.2), mul_nonneg (norm_nonneg v.2) (abs_nonneg t.1)]`.
-/
theorem norm_dot_le (v : ℂ × ℂ) (t : ℝ × ℝ) :
    ‖dot v t‖ ≤ (‖v.1‖ + ‖v.2‖) * (|t.1| + |t.2|) := by
  have h1 : ‖dot v t‖ ≤ ‖v.1‖ * |t.1| + ‖v.2‖ * |t.2| := by
    refine (norm_add_le _ _).trans ?_
    simp [norm_mul]
  have := norm_nonneg v.1
  have := norm_nonneg v.2
  have := abs_nonneg t.1
  have := abs_nonneg t.2
  nlinarith [mul_nonneg (norm_nonneg v.1) (abs_nonneg t.2), mul_nonneg (norm_nonneg v.2) (abs_nonneg t.1)]

/- English proof (translation)
Establish `h` using `Real.add_one_le_exp (ε / 2 * s)`. Establish `h2 : s = 2 / ε * (ε / 2 * s)` using `by field_simp`. Establish `h3 : ε / 2 * s ≤ Real.exp (ε / 2 * s)` using `by linarith`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem le_two_div_mul_exp {ε s : ℝ} (hε : 0 < ε) : s ≤ 2 / ε * Real.exp (ε / 2 * s) := by
  have h := Real.add_one_le_exp (ε / 2 * s)
  have h2 : s = 2 / ε * (ε / 2 * s) := by field_simp
  have h3 : ε / 2 * s ≤ Real.exp (ε / 2 * s) := by linarith
  calc s = 2 / ε * (ε / 2 * s) := h2
    _ ≤ _ := by gcongr

/- English proof (translation)
Introduce `X _ _ _ T _ φ hφ hc g p v τ₀`. Take `⟨ε, hε, U, hU, M, hM⟩` from `hφ ((p + τ₀ • v).1.re, (p + τ₀ • v).2.re) g`. Establish `hgU : g ∈ U` using `mem_of_mem_nhds hU`. Establish `hA : 0 < ‖v.1‖ + ‖v.2‖ + 1` using `by positivity`. Establish `hr : 0 < ε / (‖v.1‖ + ‖v.2‖ + 1)` using `div_pos hε hA`.

Establish `hre : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ w : ℂ, ‖w‖ ≤ ‖v.1‖ + ‖v.2‖ + 1 → ∀ q : ℂ, |(q + τ * w).re - (q + τ₀ * w).re| ≤ ε`. Introduce `τ hτ w hw q`. Establish `h1 : (q + τ * w).re - (q + τ₀ * w).re = ((τ - τ₀) * w).re`. Simplify using `only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h1]`. Use `(Complex.abs_re_le_norm _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_mul]`. Establish `h2 : ‖τ - τ₀‖ ≤ ε / (‖v.1‖ + ‖v.2‖ + 1)`. Use `Metric.mem_ball.1 hτ` as an intermediate fact.

Rewrite `this` using `[dist_eq_norm]`. Conclude with `this.le`. Combine the equalities or inequalities in the displayed calculation. Establish `key : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ t : ℝ × ℝ, ‖φ t g‖ ≤ M * Real.exp (-rdot ((p + τ • v).1.re, (p + τ • v).2.re) t) * Real.exp (-ε * (|t.1| + |t.2|))`. Introduce `τ hτ t`.

Use `hM _ ?_ ?_ g hgU t` and prove the remaining obligations. Conclude with `hre τ hτ v.1 (by linarith [norm_nonneg v.2]) p.1`. Conclude with `hre τ hτ v.2 (by linarith [norm_nonneg v.1]) p.2`. Establish `hFn : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ t : ℝ × ℝ, ‖Complex.exp (dot (p + τ • v) t) • φ t g‖ ≤ |M| * Real.exp (-ε * (|t.1| + |t.2|))`. Introduce `τ hτ t`.

Rewrite using `[norm_smul, norm_cexp_dot]`. Establish `h1` using `key τ hτ t`. Establish `h2` using `Real.exp_pos (rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.exp_neg]`.

Clear the denominators using the available nonvanishing facts. Use `_ ≤ _ := by gcongr; exact le_abs_self M`. Establish `hcont : ∀ τ : ℂ, Continuous fun t : ℝ × ℝ => Complex.exp (dot (p + τ • v) t) • φ t g`. Introduce `τ`. Use `Continuous.smul ?_ (hc g)` and prove the remaining obligations.

Simplify using `only [dot]`. Use `fun_prop`. Establish `hdotc : Continuous fun t : ℝ × ℝ => dot v t`. Unfold `dot`. Use `fun_prop`.

Establish `hint : Integrable (fun t : ℝ × ℝ => Complex.exp (dot (p + τ₀ • v) t) • φ t g)` using `(integrable_and_norm_integral_le X (fun t => φ t g) (p + τ₀ • v) ε M hε (hc g) (fun t => hM _ (by simp [hε.le]) (by simp [hε.le]) g hgU t)).1`. Establish `hbound : Integrable (fun t : ℝ × ℝ => ((‖v.1‖ + ‖v.2‖) * (2 / ε) * |M|) * (Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|)))` using `(integrable_exp_neg_abs_plane (half_pos hε)).const_mul _`. Establish `hd` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (ℝ × ℝ))) (F := fun (τ : ℂ) (t : ℝ × ℝ) => Complex.exp (dot (p + τ • v) t) • φ t g) (F' := fun (τ : ℂ) (t : ℝ × ℝ) => dot v t • (Complex.exp (dot (p + τ • v) t) • φ t g)) (x₀ := τ₀) (s := Metric.ball τ₀ (ε / …`. Rewrite using `[norm_smul]`. Establish `h1` using `norm_dot_le v t`.

Establish `h2` using `hFn τ hτ t`. Establish `h3` using `le_two_div_mul_exp (s := |t.1| + |t.2|) hε`. Establish `h4 : Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|) = Real.exp (-(ε / 2) * (|t.1| + |t.2|))`. Rewrite using `[← Real.exp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `h5 : Real.exp (ε / 2 * (|t.1| + |t.2|)) * Real.exp (-ε * (|t.1| + |t.2|)) = Real.exp (-(ε / 2) * (|t.1| + |t.2|))`. Rewrite using `[← Real.exp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h4, ← h5]`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul (h1.trans ?_) h2 (norm_nonneg _) (by positivity)` and prove the remaining obligations. Use `gcongr`. Use `_ = _ := by ring)`.

Use `hbound`. Use the proof step `(ae_of_all _ fun t τ _ => by`. Establish `h1 : HasDerivAt (fun τ : ℂ => Complex.exp (dot (p + τ • v) t)) (Complex.exp (dot (p + τ • v) t) * dot v t) τ`. Establish `h2 : HasDerivAt (fun τ : ℂ => dot p t + τ * dot v t) (dot v t) τ`. Simplify using `using ((hasDerivAt_id τ).mul_const (dot v t)).const_add (dot p t)`.

Establish `h3` using `h2.cexp`. Simplify using `only [← dot_add_smul] at h3`. Conclude with `h3`. Establish `h4` using `h1.smul_const (φ t g)`. Rewrite using `[smul_smul, mul_comm]`.

Conclude with `h4)`. Conclude with `(hd.2.differentiableAt).const_smul (((2 * Real.pi) ^ 2 : ℂ)⁻¹)`.
-/
theorem inv_differentiable_line : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ (g : T) (p v : ℂ × ℂ), Differentiable ℂ (fun τ : ℂ => inv (fun t => φ t g) (p + τ • v)) := by
  intro X _ _ _ T _ φ hφ hc g p v τ₀
  obtain ⟨ε, hε, U, hU, M, hM⟩ := hφ ((p + τ₀ • v).1.re, (p + τ₀ • v).2.re) g
  have hgU : g ∈ U := mem_of_mem_nhds hU
  have hA : 0 < ‖v.1‖ + ‖v.2‖ + 1 := by positivity
  have hr : 0 < ε / (‖v.1‖ + ‖v.2‖ + 1) := div_pos hε hA
  have hre : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ w : ℂ, ‖w‖ ≤ ‖v.1‖ + ‖v.2‖ + 1 →
      ∀ q : ℂ, |(q + τ * w).re - (q + τ₀ * w).re| ≤ ε := by
    intro τ hτ w hw q
    have h1 : (q + τ * w).re - (q + τ₀ * w).re = ((τ - τ₀) * w).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im]
      ring
    rw [h1]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have h2 : ‖τ - τ₀‖ ≤ ε / (‖v.1‖ + ‖v.2‖ + 1) := by
      have := Metric.mem_ball.1 hτ
      rw [dist_eq_norm] at this
      exact this.le
    calc ‖τ - τ₀‖ * ‖w‖ ≤ ε / (‖v.1‖ + ‖v.2‖ + 1) * (‖v.1‖ + ‖v.2‖ + 1) := by gcongr
      _ = ε := by field_simp
  have key : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ t : ℝ × ℝ,
      ‖φ t g‖ ≤ M * Real.exp (-rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
        * Real.exp (-ε * (|t.1| + |t.2|)) := by
    intro τ hτ t
    refine hM _ ?_ ?_ g hgU t
    · exact hre τ hτ v.1 (by linarith [norm_nonneg v.2]) p.1
    · exact hre τ hτ v.2 (by linarith [norm_nonneg v.1]) p.2
  have hFn : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ t : ℝ × ℝ,
      ‖Complex.exp (dot (p + τ • v) t) • φ t g‖ ≤ |M| * Real.exp (-ε * (|t.1| + |t.2|)) := by
    intro τ hτ t
    rw [norm_smul, norm_cexp_dot]
    have h1 := key τ hτ t
    have h2 := Real.exp_pos (rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
    calc _ ≤ Real.exp (rdot ((p + τ • v).1.re, (p + τ • v).2.re) t) *
          (M * Real.exp (-rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
            * Real.exp (-ε * (|t.1| + |t.2|))) := by gcongr
      _ = M * Real.exp (-ε * (|t.1| + |t.2|)) := by
        rw [Real.exp_neg]
        field_simp
      _ ≤ _ := by gcongr; exact le_abs_self M
  have hcont : ∀ τ : ℂ, Continuous fun t : ℝ × ℝ => Complex.exp (dot (p + τ • v) t) • φ t g := by
    intro τ
    refine Continuous.smul ?_ (hc g)
    simp only [dot]
    fun_prop
  have hdotc : Continuous fun t : ℝ × ℝ => dot v t := by
    unfold dot
    fun_prop
  have hint : Integrable (fun t : ℝ × ℝ => Complex.exp (dot (p + τ₀ • v) t) • φ t g) :=
    (integrable_and_norm_integral_le X (fun t => φ t g) (p + τ₀ • v) ε M hε (hc g)
      (fun t => hM _ (by simp [hε.le]) (by simp [hε.le]) g hgU t)).1
  have hbound : Integrable (fun t : ℝ × ℝ => ((‖v.1‖ + ‖v.2‖) * (2 / ε) * |M|) *
      (Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|))) :=
    (integrable_exp_neg_abs_plane (half_pos hε)).const_mul _
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (ℝ × ℝ)))
    (F := fun (τ : ℂ) (t : ℝ × ℝ) => Complex.exp (dot (p + τ • v) t) • φ t g)
    (F' := fun (τ : ℂ) (t : ℝ × ℝ) => dot v t • (Complex.exp (dot (p + τ • v) t) • φ t g))
    (x₀ := τ₀) (s := Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)))
    (bound := fun t : ℝ × ℝ => ((‖v.1‖ + ‖v.2‖) * (2 / ε) * |M|) *
      (Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|)))
    (Metric.ball_mem_nhds _ hr)
    (Eventually.of_forall fun τ => (hcont τ).aestronglyMeasurable)
    hint
    (Continuous.aestronglyMeasurable (Continuous.smul hdotc (hcont τ₀)))
    (ae_of_all _ fun t τ hτ => by
      rw [norm_smul]
      have h1 := norm_dot_le v t
      have h2 := hFn τ hτ t
      have h3 := le_two_div_mul_exp (s := |t.1| + |t.2|) hε
      have h4 : Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|)
          = Real.exp (-(ε / 2) * (|t.1| + |t.2|)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h5 : Real.exp (ε / 2 * (|t.1| + |t.2|)) * Real.exp (-ε * (|t.1| + |t.2|))
          = Real.exp (-(ε / 2) * (|t.1| + |t.2|)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h4, ← h5]
      calc _ ≤ ((‖v.1‖ + ‖v.2‖) * (2 / ε * Real.exp (ε / 2 * (|t.1| + |t.2|)))) *
            (|M| * Real.exp (-ε * (|t.1| + |t.2|))) := by
            refine mul_le_mul (h1.trans ?_) h2 (norm_nonneg _) (by positivity)
            gcongr
        _ = _ := by ring)
    hbound
    (ae_of_all _ fun t τ _ => by
      have h1 : HasDerivAt (fun τ : ℂ => Complex.exp (dot (p + τ • v) t))
          (Complex.exp (dot (p + τ • v) t) * dot v t) τ := by
        have h2 : HasDerivAt (fun τ : ℂ => dot p t + τ * dot v t) (dot v t) τ := by
          simpa using ((hasDerivAt_id τ).mul_const (dot v t)).const_add (dot p t)
        have h3 := h2.cexp
        simp only [← dot_add_smul] at h3
        exact h3
      have h4 := h1.smul_const (φ t g)
      rw [smul_smul, mul_comm]
      exact h4)
  exact (hd.2.differentiableAt).const_smul (((2 * Real.pi) ^ 2 : ℂ)⁻¹)

end GlobalTheory.CompanionTheory.TubeFourier.InvLine
