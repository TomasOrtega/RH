import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RealDiff

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.G
open scoped Classical ENNReal nonZeroDivisors

/- English proof (translation)
Use `Integrable.mono' hg.norm (hu.aestronglyMeasurable.mul hg.1) (ae_of_all _ fun ω => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (hb ω)`.
-/
private lemma bdd_int {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (u g : Ω → ℂ)
    (hu : Measurable u) (hb : ∀ ω, ‖u ω‖ ≤ 1) (hg : Integrable g ν) :
    Integrable (fun ω => u ω * g ω) ν := by
  refine Integrable.mono' hg.norm (hu.aestronglyMeasurable.mul hg.1) (ae_of_all _ fun ω => ?_)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hb ω)

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh3.real_diff ν X f hX hf G hG hGb`.
-/
private lemma real_diff {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω)
    (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) (hGb : ∀ x, ‖G x‖ ≤ 1) :
    ∫ x, G x ∂((ν.withDensity fun ω => ENNReal.ofReal (f ω)).map X)
      - ∫ x, G x ∂((ν.withDensity fun ω => ENNReal.ofReal (-f ω)).map X)
      = ∫ ω, G (X ω) * (f ω : ℂ) ∂ν :=
  _root_.UpperTheory.Reformulated.B.Qh3.real_diff ν X f hX hf G hG hGb

/- English proof (translation)
Use `haveI : IsFiniteMeasure (ν.withDensity fun ω => ENNReal.ofReal (f ω)) := isFiniteMeasure_withDensity_ofReal hf.2`. Use `haveI : IsFiniteMeasure (ν.withDensity fun ω => ENNReal.ofReal (-f ω)) := isFiniteMeasure_withDensity_ofReal hf.neg.2`. Establish `hEq : (ν.withDensity fun ω => ENNReal.ofReal (f ω)).map X = (ν.withDensity fun ω => ENNReal.ofReal (-f ω)).map X`. Use `Measure.ext_of_charFunDual (funext fun L => ?_)` and prove the remaining obligations. Rewrite using `[charFunDual_apply, charFunDual_apply]`.

Establish `key` using `real_diff ν X f hX hf (fun x => Complex.exp ((L x : ℂ) * Complex.I)) (by fun_prop) (fun x => by rw [Complex.norm_exp_ofReal_mul_I])`. Establish `h0` using `h (fun i => L (fun j => if i = j then 1 else 0))`. Establish `hL : ∀ x : ι → ℝ, L x = ∑ i, L (fun j => if i = j then 1 else 0) * x i`. Introduce `x`. Use `LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) x` as an intermediate fact.

Simplify `this` using `[mul_comm]`. Simplify using `only [← hL] at h0`. Rewrite `key` using `[h0]`. Conclude with `sub_eq_zero.mp key`. Establish `key` using `real_diff ν X f hX hf (S.indicator 1) (measurable_one.indicator hS) (fun x => by`.

Apply the tactic sequence `by_cases hx : x ∈ S <;> simp [hx])`. Rewrite `key` using `[hEq, sub_self]`. Conclude with `key.symm`.
-/
private lemma real_case {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω)
    (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (h : ∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (f ω : ℂ) ∂ν = 0)
    (S : Set (ι → ℝ)) (hS : MeasurableSet S) :
    ∫ ω, S.indicator 1 (X ω) * (f ω : ℂ) ∂ν = 0 := by
  haveI : IsFiniteMeasure (ν.withDensity fun ω => ENNReal.ofReal (f ω)) :=
    isFiniteMeasure_withDensity_ofReal hf.2
  haveI : IsFiniteMeasure (ν.withDensity fun ω => ENNReal.ofReal (-f ω)) :=
    isFiniteMeasure_withDensity_ofReal hf.neg.2
  have hEq : (ν.withDensity fun ω => ENNReal.ofReal (f ω)).map X
      = (ν.withDensity fun ω => ENNReal.ofReal (-f ω)).map X := by
    refine Measure.ext_of_charFunDual (funext fun L => ?_)
    rw [charFunDual_apply, charFunDual_apply]
    have key := real_diff ν X f hX hf (fun x => Complex.exp ((L x : ℂ) * Complex.I))
      (by fun_prop) (fun x => by rw [Complex.norm_exp_ofReal_mul_I])
    have h0 := h (fun i => L (fun j => if i = j then 1 else 0))
    have hL : ∀ x : ι → ℝ, L x = ∑ i, L (fun j => if i = j then 1 else 0) * x i := by
      intro x
      have := LinearMap.pi_apply_eq_sum_univ (L : (ι → ℝ) →ₗ[ℝ] ℝ) x
      simpa [mul_comm] using this
    simp only [← hL] at h0
    rw [h0] at key
    exact sub_eq_zero.mp key
  have key := real_diff ν X f hX hf (S.indicator 1)
    (measurable_one.indicator hS) (fun x => by
      by_cases hx : x ∈ S <;> simp [hx])
  rw [hEq, sub_self] at key
  exact key.symm

/- English proof (translation)
Introduce `Ω ι _ _ ν X ρ hX hρ h S hS`. Establish `hconjI : Integrable (fun ω => (starRingEnd ℂ) (ρ ω)) ν`. Simplify using `using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hρ`. Establish `hE : ∀ t : ι → ℝ, Measurable fun ω => Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I)`. Introduce `t`.

Establish `: ∀ i, Measurable fun ω => X ω i` using `fun i => (measurable_pi_apply i).comp hX`. Use `fun_prop`. Establish `hEb : ∀ (t : ι → ℝ) (ω : Ω), ‖Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I)‖ ≤ 1`. Introduce `t ω`. Rewrite using `[Complex.norm_exp_ofReal_mul_I]`.

Establish `hc : ∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (ρ ω) ∂ν = 0`. Introduce `t`. Establish `h1` using `congrArg (starRingEnd ℂ) (h (-t))`. Rewrite `h1` using `[← integral_conj, map_zero]`. Rewrite using `[← h1]`.

Use `integral_congr_ae (ae_of_all _ fun ω => ?_)` and prove the remaining obligations. Simplify using `only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]`. Simplify using the standard rewrite rules. Establish `hlin : ∀ (a b : ℂ) (t : ι → ℝ), ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (a * ρ ω + b * (starRingEnd ℂ) (ρ ω)) ∂ν = 0`. Introduce `a b t`.

Establish `e1` using `bdd_int ν _ ρ (hE t) (hEb t) hρ`. Establish `e2` using `bdd_int ν _ _ (hE t) (hEb t) hconjI`. Establish `: ∀ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (a * ρ ω + b * (starRingEnd ℂ) (ρ ω)) = a * (Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω) + b * (Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (ρ ω))`. Introduce `ω`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [this]`. Rewrite using `[integral_add (e1.const_mul a) (e2.const_mul b), integral_const_mul, integral_const_mul, h t, hc t]`. Simplify using the standard rewrite rules. Establish `hre : Integrable (fun ω => (ρ ω).re) ν` using `hρ.re`. Establish `him : Integrable (fun ω => (ρ ω).im) ν` using `hρ.im`.

Establish `r1` using `real_case ν X (fun ω => (ρ ω).re) hX hre (fun t => by`. Rewrite using `[← hlin (1 / 2) (1 / 2) t]`. Use `integral_congr_ae (ae_of_all _ fun ω => ?_)` and prove the remaining obligations. Establish `: ((ρ ω).re : ℂ) = 1 / 2 * ρ ω + 1 / 2 * (starRingEnd ℂ) (ρ ω)`. Rewrite using `[Complex.re_eq_add_conj]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this]) S hS`. Establish `r2` using `real_case ν X (fun ω => (ρ ω).im) hX him (fun t => by`. Rewrite using `[← hlin (1 / (2 * Complex.I)) (-(1 / (2 * Complex.I))) t]`. Use `integral_congr_ae (ae_of_all _ fun ω => ?_)` and prove the remaining obligations.

Establish `: ((ρ ω).im : ℂ) = 1 / (2 * Complex.I) * ρ ω + -(1 / (2 * Complex.I)) * (starRingEnd ℂ) (ρ ω)`. Rewrite using `[Complex.im_eq_sub_conj]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this]) S hS`. Establish `hind : Measurable fun ω => S.indicator (1 : (ι → ℝ) → ℂ) (X ω)` using `(measurable_one.indicator hS).comp hX`.

Establish `hindb : ∀ ω, ‖S.indicator (1 : (ι → ℝ) → ℂ) (X ω)‖ ≤ 1`. Introduce `ω`. Apply the tactic sequence `by_cases hx : X ω ∈ S <;> simp [hx]`. Establish `i1` using `bdd_int ν _ (fun ω => ((ρ ω).re : ℂ)) hind hindb hre.ofReal`. Establish `i2` using `bdd_int ν _ (fun ω => ((ρ ω).im : ℂ)) hind hindb him.ofReal`.

Establish `hsplit : ∀ ω, S.indicator 1 (X ω) * ρ ω = S.indicator 1 (X ω) * ((ρ ω).re : ℂ) + Complex.I * (S.indicator 1 (X ω) * ((ρ ω).im : ℂ))`. Introduce `ω`. Use `conv_lhs => rw [← Complex.re_add_im (ρ ω)]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hsplit]`.

Rewrite using `[integral_add i1 (i2.const_mul _), integral_const_mul, r1, r2]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.ConvolutionTheory.R2.G.charZero :
    ∀ (Ω ι : Type) [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (X : Ω → ι → ℝ) (ρ : Ω → ℂ), Measurable X → Integrable ρ ν →
    (∀ t : ι → ℝ, ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω ∂ν = 0) →
    ∀ S : Set (ι → ℝ), MeasurableSet S → ∫ ω, S.indicator 1 (X ω) * ρ ω ∂ν = 0 := by
  intro Ω ι _ _ ν X ρ hX hρ h S hS
  have hconjI : Integrable (fun ω => (starRingEnd ℂ) (ρ ω)) ν := by
    simpa using (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp hρ
  have hE : ∀ t : ι → ℝ, Measurable fun ω =>
      Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) := by
    intro t
    have : ∀ i, Measurable fun ω => X ω i := fun i => (measurable_pi_apply i).comp hX
    fun_prop
  have hEb : ∀ (t : ι → ℝ) (ω : Ω),
      ‖Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
    intro t ω
    rw [Complex.norm_exp_ofReal_mul_I]
  have hc : ∀ t : ι → ℝ,
      ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (ρ ω) ∂ν = 0 := by
    intro t
    have h1 := congrArg (starRingEnd ℂ) (h (-t))
    rw [← integral_conj, map_zero] at h1
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
    simp
  have hlin : ∀ (a b : ℂ) (t : ι → ℝ),
      ∫ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) *
        (a * ρ ω + b * (starRingEnd ℂ) (ρ ω)) ∂ν = 0 := by
    intro a b t
    have e1 := bdd_int ν _ ρ (hE t) (hEb t) hρ
    have e2 := bdd_int ν _ _ (hE t) (hEb t) hconjI
    have : ∀ ω, Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) *
        (a * ρ ω + b * (starRingEnd ℂ) (ρ ω))
        = a * (Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * ρ ω)
          + b * (Complex.exp (((∑ i, t i * X ω i : ℝ) : ℂ) * Complex.I) * (starRingEnd ℂ) (ρ ω)) := by
      intro ω; ring
    simp only [this]
    rw [integral_add (e1.const_mul a) (e2.const_mul b), integral_const_mul, integral_const_mul,
      h t, hc t]
    simp
  have hre : Integrable (fun ω => (ρ ω).re) ν := hρ.re
  have him : Integrable (fun ω => (ρ ω).im) ν := hρ.im
  have r1 := real_case ν X (fun ω => (ρ ω).re) hX hre (fun t => by
    rw [← hlin (1 / 2) (1 / 2) t]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have : ((ρ ω).re : ℂ) = 1 / 2 * ρ ω + 1 / 2 * (starRingEnd ℂ) (ρ ω) := by
      rw [Complex.re_eq_add_conj]; ring
    simp only [this]) S hS
  have r2 := real_case ν X (fun ω => (ρ ω).im) hX him (fun t => by
    rw [← hlin (1 / (2 * Complex.I)) (-(1 / (2 * Complex.I))) t]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    have : ((ρ ω).im : ℂ) = 1 / (2 * Complex.I) * ρ ω
        + -(1 / (2 * Complex.I)) * (starRingEnd ℂ) (ρ ω) := by
      rw [Complex.im_eq_sub_conj]; ring
    simp only [this]) S hS
  have hind : Measurable fun ω => S.indicator (1 : (ι → ℝ) → ℂ) (X ω) :=
    (measurable_one.indicator hS).comp hX
  have hindb : ∀ ω, ‖S.indicator (1 : (ι → ℝ) → ℂ) (X ω)‖ ≤ 1 := by
    intro ω
    by_cases hx : X ω ∈ S <;> simp [hx]
  have i1 := bdd_int ν _ (fun ω => ((ρ ω).re : ℂ)) hind hindb hre.ofReal
  have i2 := bdd_int ν _ (fun ω => ((ρ ω).im : ℂ)) hind hindb him.ofReal
  have hsplit : ∀ ω, S.indicator 1 (X ω) * ρ ω
      = S.indicator 1 (X ω) * ((ρ ω).re : ℂ)
        + Complex.I * (S.indicator 1 (X ω) * ((ρ ω).im : ℂ)) := by
    intro ω
    conv_lhs => rw [← Complex.re_add_im (ρ ω)]
    ring
  simp only [hsplit]
  rw [integral_add i1 (i2.const_mul _), integral_const_mul, r1, r2]
  simp
