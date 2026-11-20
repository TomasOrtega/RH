import Mathlib
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussTubeOfTubeGood
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FInt

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Yha4.main hc`.
-/
theorem integrable_exp_neg_mul_abs_alt {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|)) :=
  _root_.UpperTheory.Reformulated.B.Yha4.main hc

/- English proof (translation)
Establish `h` using `(integrable_exp_neg_mul_abs_alt hc).mul_prod (integrable_exp_neg_mul_abs_alt hc)`. Use `(h.const_mul M).congr (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Simplify using `only [mul_add, Real.exp_add]`.
-/
theorem integrable_exp_neg_mul_abs_add {c : ℝ} (hc : 0 < c) (M : ℝ) :
    Integrable (fun t : ℝ × ℝ => M * Real.exp (-c * (|t.1| + |t.2|))) := by
  have h := (integrable_exp_neg_mul_abs_alt hc).mul_prod (integrable_exp_neg_mul_abs_alt hc)
  refine (h.const_mul M).congr (Eventually.of_forall fun t => ?_)
  simp only [mul_add, Real.exp_add]

/- English proof (translation)
Rewrite using `[Complex.norm_exp]`. Simplify using `[dot, rdot]`.
-/
theorem norm_cexp_dot (l : ℂ × ℂ) (t : ℝ × ℝ) :
    ‖Complex.exp (dot l t)‖ = Real.exp (rdot (l.1.re, l.2.re) t) := by
  rw [Complex.norm_exp]
  simp [dot, rdot]

/- English proof (translation)
Introduce `X _ _ T _ _ φ hD hφ`. Rewrite using `[continuous_iff_continuousAt]`. Introduce and unpack `⟨l₀, g₀⟩`. Take `⟨ε, hε, U, hU, M, hM⟩` from `hD (l₀.1.re, l₀.2.re) g₀`. Establish `hcont : ∀ g : T, Continuous fun t : ℝ × ℝ => φ t g` using `fun g => hφ.comp (Continuous.prodMk continuous_id continuous_const)`.

Establish `hdot : ∀ t : ℝ × ℝ, Continuous fun l : ℂ × ℂ => Complex.exp (dot l t)` using `fun t => by`. Unfold `dot`. Use `fun_prop`. Establish `hdot' : ∀ l : ℂ × ℂ, Continuous fun t : ℝ × ℝ => Complex.exp (dot l t)` using `fun l => by`. Unfold `dot`.

Establish `h1 : Continuous fun t : ℝ × ℝ => ((t.1 : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp continuous_fst`. Establish `h2 : Continuous fun t : ℝ × ℝ => ((t.2 : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp continuous_snd`. Use `fun_prop`. Establish `hnear : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), |y.1.1.re - l₀.1.re| ≤ ε ∧ |y.1.2.re - l₀.2.re| ≤ ε ∧ y.2 ∈ U`. Establish `c1 : Continuous fun y : (ℂ × ℂ) × T => |y.1.1.re - l₀.1.re|` using `by fun_prop`.

Establish `c2 : Continuous fun y : (ℂ × ℂ) × T => |y.1.2.re - l₀.2.re|` using `by fun_prop`. Establish `e1 : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), |y.1.1.re - l₀.1.re| < ε` using `c1.continuousAt.eventually_lt continuousAt_const (by simpa using hε)`. Establish `e2 : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), |y.1.2.re - l₀.2.re| < ε` using `c2.continuousAt.eventually_lt continuousAt_const (by simpa using hε)`. Establish `e3 : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), y.2 ∈ U` using `continuous_snd.continuousAt.eventually (p := (· ∈ U)) hU`. Use `filter_upwards [e1, e2, e3] with y a b c using ⟨a.le, b.le, c⟩`.

Establish `key : ContinuousAt (fun y : (ℂ × ℂ) × T => ∫ t : ℝ × ℝ, Complex.exp (dot y.1 t) • φ t y.2) (l₀, g₀)`. Use `continuousAt_of_dominated (bound := fun t => M * Real.exp (-ε * (|t.1| + |t.2|))) (Eventually.of_forall fun y => ((hdot' y.1).smul (hcont y.2)).aestronglyMeasurable) ?_ (integrable_exp_neg_mul_abs_add hε M) (Eventually.of_forall fun t => ?_)` and prove the remaining obligations. Use `filter_upwards [hnear] with y hy`. Use `Eventually.of_forall fun t => ?_` and prove the remaining obligations. Establish `hb` using `hM (y.1.1.re, y.1.2.re) hy.1 hy.2.1 y.2 hy.2.2 t`.

Rewrite using `[norm_smul, norm_cexp_dot]`. Establish `hp` using `Real.exp_pos (rdot (y.1.1.re, y.1.2.re) t)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]`. Establish `h1 : Continuous fun y : (ℂ × ℂ) × T => Complex.exp (dot y.1 t)` using `(hdot t).comp continuous_fst`.

Establish `h2 : Continuous fun y : (ℂ × ℂ) × T => φ t y.2` using `hφ.comp (Continuous.prodMk continuous_const continuous_snd)`. Conclude with `(h1.smul h2).continuousAt`. Conclude with `continuousAt_const.smul key`.
-/
theorem inv_continuous_joint : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type)
    [TopologicalSpace T] [FirstCountableTopology T] (φ : ℝ × ℝ → T → X), ExpDecay φ →
    Continuous (fun p : (ℝ × ℝ) × T => φ p.1 p.2) →
    Continuous (fun y : (ℂ × ℂ) × T => inv (fun t => φ t y.2) y.1) := by
  intro X _ _ T _ _ φ hD hφ
  rw [continuous_iff_continuousAt]
  rintro ⟨l₀, g₀⟩
  obtain ⟨ε, hε, U, hU, M, hM⟩ := hD (l₀.1.re, l₀.2.re) g₀
  have hcont : ∀ g : T, Continuous fun t : ℝ × ℝ => φ t g := fun g =>
    hφ.comp (Continuous.prodMk continuous_id continuous_const)
  have hdot : ∀ t : ℝ × ℝ, Continuous fun l : ℂ × ℂ => Complex.exp (dot l t) := fun t => by
    unfold dot
    fun_prop
  have hdot' : ∀ l : ℂ × ℂ, Continuous fun t : ℝ × ℝ => Complex.exp (dot l t) := fun l => by
    unfold dot
    have h1 : Continuous fun t : ℝ × ℝ => ((t.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_fst
    have h2 : Continuous fun t : ℝ × ℝ => ((t.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_snd
    fun_prop
  have hnear : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀),
      |y.1.1.re - l₀.1.re| ≤ ε ∧ |y.1.2.re - l₀.2.re| ≤ ε ∧ y.2 ∈ U := by
    have c1 : Continuous fun y : (ℂ × ℂ) × T => |y.1.1.re - l₀.1.re| := by fun_prop
    have c2 : Continuous fun y : (ℂ × ℂ) × T => |y.1.2.re - l₀.2.re| := by fun_prop
    have e1 : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), |y.1.1.re - l₀.1.re| < ε :=
      c1.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    have e2 : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), |y.1.2.re - l₀.2.re| < ε :=
      c2.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    have e3 : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), y.2 ∈ U :=
      continuous_snd.continuousAt.eventually (p := (· ∈ U)) hU
    filter_upwards [e1, e2, e3] with y a b c using ⟨a.le, b.le, c⟩
  have key : ContinuousAt (fun y : (ℂ × ℂ) × T =>
      ∫ t : ℝ × ℝ, Complex.exp (dot y.1 t) • φ t y.2) (l₀, g₀) := by
    refine continuousAt_of_dominated (bound := fun t => M * Real.exp (-ε * (|t.1| + |t.2|)))
      (Eventually.of_forall fun y => ((hdot' y.1).smul (hcont y.2)).aestronglyMeasurable)
      ?_ (integrable_exp_neg_mul_abs_add hε M)
      (Eventually.of_forall fun t => ?_)
    · filter_upwards [hnear] with y hy
      refine Eventually.of_forall fun t => ?_
      have hb := hM (y.1.1.re, y.1.2.re) hy.1 hy.2.1 y.2 hy.2.2 t
      rw [norm_smul, norm_cexp_dot]
      have hp := Real.exp_pos (rdot (y.1.1.re, y.1.2.re) t)
      calc Real.exp (rdot (y.1.1.re, y.1.2.re) t) * ‖φ t y.2‖
          ≤ Real.exp (rdot (y.1.1.re, y.1.2.re) t) *
            (M * Real.exp (-rdot (y.1.1.re, y.1.2.re) t) * Real.exp (-ε * (|t.1| + |t.2|))) := by
            gcongr
        _ = M * (Real.exp (rdot (y.1.1.re, y.1.2.re) t) * Real.exp (-rdot (y.1.1.re, y.1.2.re) t)) *
            Real.exp (-ε * (|t.1| + |t.2|)) := by ring
        _ = M * Real.exp (-ε * (|t.1| + |t.2|)) := by
            rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    · have h1 : Continuous fun y : (ℂ × ℂ) × T => Complex.exp (dot y.1 t) :=
        (hdot t).comp continuous_fst
      have h2 : Continuous fun y : (ℂ × ℂ) × T => φ t y.2 :=
        hφ.comp (Continuous.prodMk continuous_const continuous_snd)
      exact (h1.smul h2).continuousAt
  exact continuousAt_const.smul key

end GlobalTheory.CompanionTheory.TubeFourier
