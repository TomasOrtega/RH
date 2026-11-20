import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAApply
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SummableLatticeExpNegPiMulNormSqDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierHarmonicMonomialMulGaussianComplexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierProdSingleCoordinateFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCompCoordDilationByHalfExpStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeIdealEuclideanLatticeIsZLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianHarmonicProductKernelContinuousBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumRingEqSumIdealCosetsTsumStatement

noncomputable section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory.HeckePoisson

open GlobalTheory.HeckeTheta

variable {I : Type} [Fintype I]

/- English proof (translation)
Simplify using `[gauss]`.
-/
theorem gauss_unit (k : ℤ) (z : ℂ) :
    gauss (fun _ : Unit => k) (fun _ => z) = hmon k z * Complex.exp ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  simp [gauss]

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq]`. Simplify using the standard rewrite rules.
-/
theorem norm_toLp_unit (z : ℂ) : ‖(WithLp.toLp 2 (fun _ : Unit => z) : EuclideanSpace ℂ Unit)‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq]; simp

/- English proof (translation)
Take `⟨hc, C, hC⟩` from `GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded Unit (fun _ => k)`. Establish `hcont : Continuous (fun z : ℂ => hmon k z * Complex.exp ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ))`. Establish `: Continuous (fun z : ℂ => (WithLp.toLp 2 (fun _ : Unit => z) : EuclideanSpace ℂ Unit))` using `by fun_prop`. Simplify `hc.comp this` using `[Function.comp_def, gauss_unit]`. Establish `hint : Integrable (fun z : ℂ => C * Real.exp (-Real.pi * ‖z‖ ^ 2))`.

Use `(GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos) 0 0).norm` as an intermediate fact. Use `(this.const_mul C).congr (ae_of_all _ fun z => ?_)` and prove the remaining obligations. Simplify using `only [inner_zero_left, Complex.norm_exp]`. Use `congr 2`. Simplify using `[← Complex.ofReal_pow]`.

Use `hint.mono' hcont.aestronglyMeasurable (ae_of_all _ fun z => ?_)` and prove the remaining obligations. Establish `h` using `hC (WithLp.toLp 2 (fun _ : Unit => z))`. Rewrite `h` using `[norm_toLp_unit]`. Simplify `h` using `[gauss_unit]`.
-/
theorem integrable_hmon_gauss (k : ℤ) :
    Integrable (fun z : ℂ => hmon k z * Complex.exp ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ)) := by
  obtain ⟨hc, C, hC⟩ := GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded Unit (fun _ => k)
  have hcont : Continuous (fun z : ℂ => hmon k z * Complex.exp ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ)) := by
    have : Continuous (fun z : ℂ => (WithLp.toLp 2 (fun _ : Unit => z) : EuclideanSpace ℂ Unit)) := by fun_prop
    simpa [Function.comp_def, gauss_unit] using hc.comp this
  have hint : Integrable (fun z : ℂ => C * Real.exp (-Real.pi * ‖z‖ ^ 2)) := by
    have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (Real.pi : ℂ)) (by simpa using Real.pi_pos) 0 0).norm
    refine (this.const_mul C).congr (ae_of_all _ fun z => ?_)
    simp only [inner_zero_left, Complex.norm_exp]
    congr 2
    simp [← Complex.ofReal_pow]
  refine hint.mono' hcont.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  have h := hC (WithLp.toLp 2 (fun _ : Unit => z))
  rw [norm_toLp_unit] at h
  simpa [gauss_unit] using h

/- English proof (translation)
Establish `h` using `GlobalTheory.T.fourier_prod_single_coordinate_functions I (fun i z => hmon (n i) z * Complex.exp ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ)) (fun i => integrable_hmon_gauss (n i)) l`. Establish `e : (fun w : EuclideanSpace ℂ I => gauss n (WithLp.ofLp w)) = fun w => ∏ i, (hmon (n i) (w i) * Complex.exp ((-2 * Real.pi * ‖w i‖ ^ 2 : ℝ) : ℂ))` using `rfl`. Rewrite using `[e, h]`. Simplify using `only [GlobalTheory.T.fourier_harmonicMonomial_mul_gaussian_complex]`. Unfold `kappa gauss`.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.card_univ]`. Simplify using `[one_div, inv_pow]`.
-/
theorem fourier_gauss (n : I → ℤ) (l : EuclideanSpace ℂ I) :
    𝓕 (fun w : EuclideanSpace ℂ I => gauss n (WithLp.ofLp w)) l = kappa n * gauss n (fun i => l i / 2) := by
  have h := GlobalTheory.T.fourier_prod_single_coordinate_functions I (fun i z => hmon (n i) z * Complex.exp ((-2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ))
    (fun i => integrable_hmon_gauss (n i)) l
  have e : (fun w : EuclideanSpace ℂ I => gauss n (WithLp.ofLp w)) =
      fun w => ∏ i, (hmon (n i) (w i) * Complex.exp ((-2 * Real.pi * ‖w i‖ ^ 2 : ℝ) : ℂ)) := rfl
  rw [e, h]
  simp only [GlobalTheory.T.fourier_harmonicMonomial_mul_gaussian_complex]
  unfold kappa gauss
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum, Finset.card_univ]
  simp [one_div, inv_pow]

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Establish `h` using `norm_le_pi_norm (fun i => l i / 2 : I → ℂ) i`. Establish `h2 : ‖l i‖ = 2 * ‖(fun i => l i / 2 : I → ℂ) i‖`.

Simplify using `only [norm_div, Complex.norm_ofNat]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Use polynomial arithmetic with `[norm_nonneg ((fun i => l i / 2 : I → ℂ) i)]`. Use `_ = 4 * Fintype.card I * ‖(fun i => l i / 2 : I → ℂ)‖ ^ 2 := by`.

Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_half_sq (l : EuclideanSpace ℂ I) :
    ‖l‖ ^ 2 ≤ 4 * Fintype.card I * ‖(fun i => l i / 2 : I → ℂ)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ i, ‖l i‖ ^ 2 ≤ ∑ _i : I, 4 * ‖(fun i => l i / 2 : I → ℂ)‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := norm_le_pi_norm (fun i => l i / 2 : I → ℂ) i
        have h2 : ‖l i‖ = 2 * ‖(fun i => l i / 2 : I → ℂ) i‖ := by
          simp only [norm_div, Complex.norm_ofNat]; ring
        rw [h2]
        nlinarith [norm_nonneg ((fun i => l i / 2 : I → ℂ) i)]
    _ = 4 * Fintype.card I * ‖(fun i => l i / 2 : I → ℂ)‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/- English proof (translation)
Establish `: (WithLp.toLp 2 (fun i => l i / 2) : EuclideanSpace ℂ I) = (2⁻¹ : ℝ) • l`. Use extensionality with `i`. Simplify using `[div_eq_mul_inv, mul_comm]`. Rewrite using `[this, norm_smul]`. Simplify using `[div_eq_inv_mul]`.
-/
theorem norm_toLp_half (l : EuclideanSpace ℂ I) :
    ‖(WithLp.toLp 2 (fun i => l i / 2) : EuclideanSpace ℂ I)‖ = ‖l‖ / 2 := by
  have : (WithLp.toLp 2 (fun i => l i / 2) : EuclideanSpace ℂ I) = (2⁻¹ : ℝ) • l := by
    ext i; simp [div_eq_mul_inv, mul_comm]
  rw [this, norm_smul]; simp [div_eq_inv_mul]

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Establish `he : Real.exp (y i / 2) ^ 2 = Real.exp (y i)` using `by rw [sq, ← Real.exp_add, add_halves]`. Establish `h1 : ‖(WithLp.toLp 2 (dil y (WithLp.ofLp w)) : EuclideanSpace ℂ I) i‖ ^ 2 = Real.exp (y i) * ‖w i‖ ^ 2`. Simplify using `only [dil, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, he]`.

Rewrite using `[h1]`. Use `mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)` and prove the remaining obligations. Use `Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)` as an intermediate fact. Use `neg_abs_le (y i)` as an intermediate fact. Simplify using `only at *`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_dil_sq_ge (y : I → ℝ) (w : EuclideanSpace ℂ I) :
    Real.exp (-∑ i, |y i|) * ‖w‖ ^ 2 ≤ ‖(WithLp.toLp 2 (dil y (WithLp.ofLp w)) : EuclideanSpace ℂ I)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have he : Real.exp (y i / 2) ^ 2 = Real.exp (y i) := by rw [sq, ← Real.exp_add, add_halves]
  have h1 : ‖(WithLp.toLp 2 (dil y (WithLp.ofLp w)) : EuclideanSpace ℂ I) i‖ ^ 2 = Real.exp (y i) * ‖w i‖ ^ 2 := by
    simp only [dil, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, he]
  rw [h1]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (by positivity)
  have := Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have := neg_abs_le (y i)
  simp only at *
  linarith

/- English proof (translation)
Take `⟨-, C, hC⟩` from `GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded I n`. Establish `hC0 : 0 ≤ C`. Establish `h` using `(norm_nonneg _).trans (hC 0)`. Conclude with `le_of_mul_le_mul_right (by rw [zero_mul]; exact h) (Real.exp_pos _)`. Use `⟨C, Real.pi * Real.exp (-∑ i, |y i|), hC0, by positivity, fun w => ?_⟩` and prove the remaining obligations.

Establish `h` using `hC (WithLp.toLp 2 (dil y (WithLp.ofLp w)))`. Use `h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0)` and prove the remaining obligations. Use `norm_dil_sq_ge y w` as an intermediate fact. Use polynomial arithmetic with `[Real.pi_pos]`.
-/
theorem gauss_dil_bound (n : I → ℤ) (y : I → ℝ) : ∃ C a : ℝ, 0 ≤ C ∧ 0 < a ∧ ∀ w : EuclideanSpace ℂ I,
    ‖gauss n (dil y (WithLp.ofLp w))‖ ≤ C * Real.exp (-a * ‖w‖ ^ 2) := by
  obtain ⟨-, C, hC⟩ := GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded I n
  have hC0 : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hC 0)
    exact le_of_mul_le_mul_right (by rw [zero_mul]; exact h) (Real.exp_pos _)
  refine ⟨C, Real.pi * Real.exp (-∑ i, |y i|), hC0, by positivity, fun w => ?_⟩
  have h := hC (WithLp.toLp 2 (dil y (WithLp.ofLp w)))
  refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0)
  have := norm_dil_sq_ge y w
  nlinarith [Real.pi_pos]

/- English proof (translation)
Use `set f : EuclideanSpace ℂ I → ℂ := fun w => gauss n (dil y (WithLp.ofLp w)) with hf`. Establish `hF : ∀ l : EuclideanSpace ℂ I, 𝓕 f l = (Real.exp (-∑ i, y i) : ℂ) * kappa n * gauss n (dil (-y) (fun i => l i / 2))`. Introduce `l`. Establish `h` using `GlobalTheory.T.fourier_comp_coordDilationByHalfExp I (fun w => gauss n (WithLp.ofLp w)) y l`. Rewrite using `[hf, h, fourier_gauss, mul_assoc]`.

Use `congr 3`. Use function extensionality and compare the values at `i`. Simplify using `only [dil]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨C, a, hC0, ha, hC⟩` from `gauss_dil_bound n y`.

Take `⟨C', a', hC0', ha', hC'⟩` from `gauss_dil_bound n (-y)`. Establish `hcont : Continuous f`. Establish `h1` using `(GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded I n).1`. Establish `h2 : Continuous (fun w : EuclideanSpace ℂ I => (WithLp.toLp 2 (dil y (WithLp.ofLp w)) : EuclideanSpace ℂ I))`. Unfold `dil`.

Use `fun_prop`. Establish `h3` using `h1.comp h2`. Simplify `h3` using `only [Function.comp_def, WithLp.ofLp_toLp, hf]`. Establish `hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (v : EuclideanSpace ℂ I), ‖v‖ ≤ R → ‖f (x + v)‖ ≤ g x`. Introduce `R`.

Use `⟨fun x => C * (Real.exp (a * R ^ 2) * Real.exp (-(a / 2) * ‖(x : EuclideanSpace ℂ I)‖ ^ 2)), ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left _).mul_left _, fun x v hv => ?_⟩` and prove the remaining obligations. Conclude with `(hC _).trans (mul_le_mul_of_nonneg_left (GlobalTheory.exp_neg_mul_norm_add_sq_le ha.le _ hv) hC0)`. Establish `hG : Summable (fun l : GlobalTheory.dualLattice L => ‖gauss n (dil (-y) (fun i => (l : EuclideanSpace ℂ I) i / 2))‖)`. Use `.of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_) ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq (GlobalTheory.dualLattice L) (div_pos ha' (by norm_num : (0:ℝ) < 4))).mul_left C')` and prove the remaining obligations. Establish `h` using `hC' (WithLp.toLp 2 (fun i => (l : EuclideanSpace ℂ I) i / 2))`.

Rewrite `h` using `[norm_toLp_half]`. Use `h.trans_eq ?_` and prove the remaining obligations. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `hs : Summable fun l : GlobalTheory.dualLattice L => ‖𝓕 f l‖`.

Simplify using `only [hF, norm_mul]`. Conclude with `hG.mul_left _`. Use `⟨hG, ?_⟩` and prove the remaining obligations. Establish `hP` using `GlobalTheory.tsum_poisson_lattice L hcont hdom hs u`. Simplify using `only [hf] at hP`.

Rewrite using `[hP, Complex.real_smul, Complex.ofReal_inv, ← tsum_mul_left, ← tsum_mul_left]`. Use `tsum_congr fun l => ?_` and prove the remaining obligations. Rewrite using `[smul_eq_mul, (hF l : 𝓕 (fun w : EuclideanSpace ℂ I => gauss n (dil y (WithLp.ofLp w))) l = _)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem poisson_coset (L : Submodule ℤ (EuclideanSpace ℂ I)) [DiscreteTopology L] [IsZLattice ℝ L]
    (n : I → ℤ) (y : I → ℝ) (u : EuclideanSpace ℂ I) :
    Summable (fun l : GlobalTheory.dualLattice L => ‖gauss n (dil (-y) (fun i => (l : EuclideanSpace ℂ I) i / 2))‖) ∧
    ∑' x : L, gauss n (dil y (WithLp.ofLp ((x : EuclideanSpace ℂ I) + u))) =
      ((ZLattice.covolume L : ℝ) : ℂ)⁻¹ * ((Real.exp (-∑ i, y i) : ℂ) * kappa n) *
        ∑' l : GlobalTheory.dualLattice L, Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u⟫ : ℝ) : ℂ)) *
          gauss n (dil (-y) (fun i => (l : EuclideanSpace ℂ I) i / 2)) := by
  set f : EuclideanSpace ℂ I → ℂ := fun w => gauss n (dil y (WithLp.ofLp w)) with hf
  have hF : ∀ l : EuclideanSpace ℂ I, 𝓕 f l =
      (Real.exp (-∑ i, y i) : ℂ) * kappa n * gauss n (dil (-y) (fun i => l i / 2)) := by
    intro l
    have h := GlobalTheory.T.fourier_comp_coordDilationByHalfExp I (fun w => gauss n (WithLp.ofLp w)) y l
    rw [hf, h, fourier_gauss, mul_assoc]
    congr 3
    funext i
    simp only [dil]
    ring
  obtain ⟨C, a, hC0, ha, hC⟩ := gauss_dil_bound n y
  obtain ⟨C', a', hC0', ha', hC'⟩ := gauss_dil_bound n (-y)
  have hcont : Continuous f := by
    have h1 := (GlobalTheory.T.gaussianHarmonicProductKernel_continuous_bounded I n).1
    have h2 : Continuous (fun w : EuclideanSpace ℂ I => (WithLp.toLp 2 (dil y (WithLp.ofLp w)) : EuclideanSpace ℂ I)) := by
      unfold dil; fun_prop
    have h3 := h1.comp h2
    simpa only [Function.comp_def, WithLp.ofLp_toLp, hf] using h3
  have hdom : ∀ R : ℝ, ∃ g : L → ℝ, Summable g ∧ ∀ (x : L) (v : EuclideanSpace ℂ I), ‖v‖ ≤ R → ‖f (x + v)‖ ≤ g x := by
    intro R
    refine ⟨fun x => C * (Real.exp (a * R ^ 2) * Real.exp (-(a / 2) * ‖(x : EuclideanSpace ℂ I)‖ ^ 2)),
      ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq L (half_pos ha)).mul_left _).mul_left _, fun x v hv => ?_⟩
    exact (hC _).trans (mul_le_mul_of_nonneg_left (GlobalTheory.exp_neg_mul_norm_add_sq_le ha.le _ hv) hC0)
  have hG : Summable (fun l : GlobalTheory.dualLattice L => ‖gauss n (dil (-y) (fun i => (l : EuclideanSpace ℂ I) i / 2))‖) := by
    refine .of_nonneg_of_le (fun _ => norm_nonneg _) (fun l => ?_)
      ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq (GlobalTheory.dualLattice L) (div_pos ha' (by norm_num : (0:ℝ) < 4))).mul_left C')
    have h := hC' (WithLp.toLp 2 (fun i => (l : EuclideanSpace ℂ I) i / 2))
    rw [norm_toLp_half] at h
    refine h.trans_eq ?_
    congr 2
    ring
  have hs : Summable fun l : GlobalTheory.dualLattice L => ‖𝓕 f l‖ := by
    simp only [hF, norm_mul]
    exact hG.mul_left _
  refine ⟨hG, ?_⟩
  have hP := GlobalTheory.tsum_poisson_lattice L hcont hdom hs u
  simp only [hf] at hP
  rw [hP, Complex.real_smul, Complex.ofReal_inv, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  rw [smul_eq_mul, (hF l : 𝓕 (fun w : EuclideanSpace ℂ I => gauss n (dil y (WithLp.ofLp w))) l = _)]
  ring

/- English proof (translation)
Take `⟨r, hr, h⟩` from `Metric.isOpen_singleton_iff.1 (isOpen_discrete ({0} : Set L))`. Use `⟨r, hr, fun x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Conclude with `hx (h x (by rw [dist_zero_right]; exact hlt))`.
-/
theorem discrete_norm_ge {E : Type} [NormedAddCommGroup E] (L : Submodule ℤ E) [DiscreteTopology L] :
    ∃ r : ℝ, 0 < r ∧ ∀ x : L, x ≠ 0 → r ≤ ‖(x : E)‖ := by
  obtain ⟨r, hr, h⟩ := Metric.isOpen_singleton_iff.1 (isOpen_discrete ({0} : Set L))
  refine ⟨r, hr, fun x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  exact hx (h x (by rw [dist_zero_right]; exact hlt))

/- English proof (translation)
Introduce `K _ _ _ I _ φ hφ n M F hM hF`. Take `⟨hd, hz⟩` from `GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice K I φ hφ M hM`. Use `haveI : Finite (𝓞 K ⧸ M) := Ideal.finiteQuotientOfFreeOfNeBot M hM`. Use `letI : Fintype (𝓞 K ⧸ M) := Fintype.ofFinite _`. Use `set L := lat φ M with hL`.

Use `set D := GlobalTheory.dualLattice L with hD`. Establish `hI : Nonempty I`. Take `⟨σ⟩ : Nonempty (K →+* ℂ)` from `inferInstance`. Take `⟨i, -, -⟩` from `hφ σ`. Conclude with `⟨i⟩`.

Establish `hinj : Function.Injective (embA φ)`. Introduce `x x' h`. Take `⟨i⟩` from `hI`. Establish `h2` using `congrArg (fun z : EuclideanSpace ℂ I => z i) h`. Simplify using `only [embA_apply] at h2`.

Conclude with `RingOfIntegers.ext ((φ i).injective h2)`. Use `set u : 𝓞 K ⧸ M → EuclideanSpace ℂ I := fun c => embA φ (Quotient.out c) with hu`. Use `set half : D → (I → ℂ) := fun l i => (l : EuclideanSpace ℂ I) i / 2 with hhalf_def`. Establish `hhalf : Function.Injective half`. Introduce `l l' h`.

Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i`. Use `congrFun h i` as an intermediate fact. Simplify using `only [hhalf_def] at this`. Take the linear combination `2 * this`.

Use `set cov : ℂ := ((ZLattice.covolume L : ℝ) : ℂ) with hcov`. Use `set A : D → ℂ := fun l => cov⁻¹ * ∑ c : 𝓞 K ⧸ M, F (Quotient.out c) * Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ)) with hA`. Use `set a : (I → ℂ) → ℂ := fun v => if h : ∃ l : D, half l = v then A (Classical.choose h) else 0 with ha_def`. Establish `ha_half : ∀ l, a (half l) = A l`. Introduce `l`.

Establish `h : ∃ l' : D, half l' = half l` using `⟨l, rfl⟩`. Simplify using `only [ha_def, dif_pos h]`. Rewrite using `[hhalf (Classical.choose_spec h)]`. Establish `ha_zero : ∀ v, v ∉ Set.range half → a v = 0`. Introduce `v hv`.

Establish `h : ¬ ∃ l : D, half l = v` using `fun ⟨l, hl⟩ => hv ⟨l, hl⟩`. Simplify using `only [ha_def, dif_neg h]`. Use `set B : ℝ := ‖cov⁻¹‖ * ∑ c : 𝓞 K ⧸ M, ‖F (Quotient.out c)‖ with hB`. Establish `hB0 : 0 ≤ B` using `by positivity`. Establish `hAB : ∀ l, ‖A l‖ ≤ B`.

Introduce `l`. Simplify using `only [hA, hB, norm_mul]`. Use `mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)) (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[norm_mul, GlobalTheory.norm_cexp_two_pi_I, mul_one]`. Use `set cI : ℝ := (Fintype.card I : ℝ) with hcI`.

Establish `hcI0 : 0 ≤ cI` using `by positivity`. Establish `hnorm : ∀ l : D, ‖(l : EuclideanSpace ℂ I)‖ ^ 2 ≤ (4 * cI + 1) * ‖half l‖ ^ 2`. Introduce `l`. Use `norm_half_sq (l : EuclideanSpace ℂ I)` as an intermediate fact. Use polynomial arithmetic with `[sq_nonneg ‖half l‖]`.

Use `⟨a, kappa n, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `ε hε`. Establish `hpos : 0 < ε / (4 * cI + 1)` using `by positivity`. Establish `key : Summable (fun l : D => ‖a (half l)‖ * Real.exp (-ε * ‖half l‖ ^ 2))`. Use `.of_nonneg_of_le (fun _ => by positivity) (fun l => ?_) ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq D hpos).mul_left B)` and prove the remaining obligations.

Rewrite using `[ha_half]`. Use `mul_le_mul (hAB l) (Real.exp_le_exp.2 ?_) (by positivity) hB0` and prove the remaining obligations. Establish `h1` using `hnorm l`. Establish `h2 : ε / (4 * cI + 1) * ‖(l : EuclideanSpace ℂ I)‖ ^ 2 ≤ ε * ‖half l‖ ^ 2`. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(hhalf.summable_iff (f := fun v => ‖a v‖ * Real.exp (-ε * ‖v‖ ^ 2)) (fun v hv => by simp [ha_zero v hv])).1 key`. Take `⟨r, hr, hr'⟩` from `discrete_norm_ge (GlobalTheory.dualLattice L)`. Use `⟨r / (4 * cI + 1), by positivity, fun v hav hv0 => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hv : v ∈ Set.range half`. Take `⟨l, rfl⟩` from `hv`. Establish `hl0 : l ≠ 0`. Introduce and unpack `rfl`. Apply `hv0` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Simplify using `[hhalf_def]`. Establish `h1 : r ≤ ‖(l : EuclideanSpace ℂ I)‖` using `hr' ⟨l, l.2⟩ (fun h => hl0 (Subtype.ext (congrArg Subtype.val h)))`. Establish `h2` using `hnorm l`. Establish `h3 : r ^ 2 ≤ ((4 * cI + 1) * ‖half l‖) ^ 2`.

Establish `: r ^ 2 ≤ ‖(l : EuclideanSpace ℂ I)‖ ^ 2` using `pow_le_pow_left₀ hr.le h1 2`. Establish `h4 : (4 * cI + 1) * ‖half l‖ ^ 2 ≤ ((4 * cI + 1) * ‖half l‖) ^ 2`. Rewrite using `[mul_pow]`. Establish `: (4 * cI + 1) ≤ (4 * cI + 1) ^ 2` using `by nlinarith`. Conclude with `mul_le_mul_of_nonneg_right this (sq_nonneg _)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : r ≤ (4 * cI + 1) * ‖half l‖` using `(pow_le_pow_iff_left₀ hr.le (by positivity) two_ne_zero).1 h3`. Rewrite using `[div_le_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `absurd (ha_zero v hv) hav`.

Introduce `y`. Take `⟨hd', hz'⟩` from `GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice K I φ hφ ⊤ (by simp)`. Take `⟨C, b, hC0, hb, hC⟩` from `gauss_dil_bound n y`. Use `set BF : ℝ := ∑ c : 𝓞 K ⧸ M, ‖F (Quotient.out c)‖ with hBF`. Establish `hFc : ∀ α : 𝓞 K, F α = F (Quotient.out (Ideal.Quotient.mk M α))`.

Introduce `α`. Establish `hm : α - Quotient.out (Ideal.Quotient.mk M α) ∈ M`. Rewrite using `[← Ideal.Quotient.eq, Ideal.Quotient.mk_out]`. Use `hF (Quotient.out (Ideal.Quotient.mk M α)) _ hm` as an intermediate fact. Rewrite `this` using `[add_sub_cancel]`.

Conclude with `this`. Establish `hFB : ∀ α : 𝓞 K, ‖F α‖ ≤ BF`. Introduce `α`. Rewrite using `[hFc α]`. Conclude with `Finset.single_le_sum (f := fun c => ‖F (Quotient.out c)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)`.

Establish `hemb : ∀ α : 𝓞 K, emb φ (α : K) = WithLp.ofLp (embA φ α)` using `fun α => rfl`. Establish `hsum : Summable (fun α : 𝓞 K => F α * gauss n (dil y (emb φ (α : K))))`. Establish `hT : Summable (fun x : lat φ ⊤ => BF * (C * Real.exp (-b * ‖(x : EuclideanSpace ℂ I)‖ ^ 2)))` using `((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq (lat φ ⊤) hb).mul_left C).mul_left BF`. Establish `hi : Function.Injective (fun α : 𝓞 K => (⟨embA φ α, mem_lat.2 ⟨α, Submodule.mem_top, rfl⟩⟩ : lat φ ⊤))` using `fun x x' h => hinj (congrArg Subtype.val h)`. Use `Summable.of_norm_bounded (hT.comp_injective hi) (fun α => ?_)` and prove the remaining obligations.

Simplify using `only [Function.comp_apply, norm_mul]`. Conclude with `mul_le_mul (hFB α) (hC (embA φ α)) (norm_nonneg _) (by positivity)`. Set `e : M ≃ L` to `Equiv.ofBijective (fun μ => (⟨embA φ μ, mem_lat.2 ⟨μ, μ.2, rfl⟩⟩ : L)) ⟨fun x x' h => Subtype.ext (hinj (congrArg Subtype.val h)), fun x => by`. Take `⟨μ, hμ, h⟩` from `mem_lat.1 x.2`. Conclude with `⟨⟨μ, hμ⟩, Subtype.ext h⟩⟩`.

Establish `hcoset : ∀ c : 𝓞 K ⧸ M, ∑' μ : M, F (Quotient.out c + μ) * gauss n (dil y (emb φ ((Quotient.out c + μ : 𝓞 K) : K))) = F (Quotient.out c) * (cov⁻¹ * ((Real.exp (-∑ i, y i) : ℂ) * kappa n) * ∑' l : D, Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ …`. Introduce `c`. Establish `h1 : ∀ μ : M, F (Quotient.out c + μ) * gauss n (dil y (emb φ ((Quotient.out c + μ : 𝓞 K) : K))) = F (Quotient.out c) * gauss n (dil y (WithLp.ofLp (((e μ : L) : EuclideanSpace ℂ I) + u c)))`. Introduce `μ`. Rewrite using `[hF _ _ μ.2]`.

Establish `hx : emb φ ((Quotient.out c + μ : 𝓞 K) : K) = WithLp.ofLp (((e μ : L) : EuclideanSpace ℂ I) + u c)`. Use function extensionality and compare the values at `i`. Use `show φ i ((Quotient.out c + μ : 𝓞 K) : K) = (embA φ μ + embA φ (Quotient.out c)) i`. Rewrite using `[PiLp.add_apply, embA_apply, embA_apply]`. Use `push_cast`.

Rewrite using `[map_add, add_comm]`. Rewrite using `[hx]`. Rewrite using `[tsum_congr h1, tsum_mul_left, e.tsum_eq (fun x : L => gauss n (dil y (WithLp.ofLp ((x : EuclideanSpace ℂ I) + u c)))), (poisson_coset L n y (u c)).2]`. Establish `hLHS` using `GlobalTheory.T.tsum_ring_eq_sum_ideal_cosets_tsum (𝓞 K) M _ hsum`. Unfold `GlobalTheory.HeckeTheta.theta`.

Rewrite using `[hLHS, Finset.sum_congr rfl (fun c _ => hcoset c)]`. Establish `hsupp : Function.support (fun v : I → ℂ => a v * gauss n (dil (-y) v)) ⊆ Set.range half`. Introduce `v hv`. Assume the negation of the conclusion as `h`. Conclude with `hv (by simp [ha_zero v h])`.

Rewrite using `[← hhalf.tsum_eq hsupp]`. Simplify using `only [ha_half, hA]`. Establish `hsc : ∀ c ∈ (Finset.univ : Finset (𝓞 K ⧸ M)), Summable (fun l : D => cov⁻¹ * (F (Quotient.out c) * Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l)))`. Introduce `c _`. Use `Summable.of_norm_bounded (((poisson_coset L n y (u c)).1).mul_left (‖cov⁻¹‖ * ‖F (Quotient.out c)‖)) (fun l => ?_)` and prove the remaining obligations.

Rewrite using `[norm_mul, norm_mul, norm_mul, GlobalTheory.norm_cexp_two_pi_I, mul_one]`. Establish `hre : ∀ l : D, cov⁻¹ * (∑ c : 𝓞 K ⧸ M, F (Quotient.out c) * Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l)) = ∑ c : 𝓞 K ⧸ M, cov⁻¹ * (F (Quotient.out c) * Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSp …`. Introduce `l`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[tsum_congr hre, Summable.tsum_finsetSum hsc, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Establish `hre2 : ∀ l : D, cov⁻¹ * (F (Quotient.out c) * Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l)) = (cov⁻¹ * F (Quotient.out c)) * (Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ)) * …` using `fun l => by ring`. Rewrite using `[tsum_congr hre2, tsum_mul_left]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theta_poisson : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (M : Ideal (NumberField.RingOfIntegers K))
    (F : NumberField.RingOfIntegers K → ℂ), M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) →
    ∃ (a : (I → ℂ) → ℂ) (κ : ℂ), (∀ ε : ℝ, 0 < ε → Summable (fun v => ‖a v‖ * Real.exp (-ε * ‖v‖ ^ 2))) ∧
      (∃ δ : ℝ, 0 < δ ∧ ∀ v, a v ≠ 0 → v ≠ 0 → δ ≤ ‖v‖) ∧
      ∀ y : I → ℝ, GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y =
        κ * (Real.exp (-∑ i, y i) : ℂ) * GlobalTheory.HeckeTheta.theta (fun v : I → ℂ => v) a n (-y) := by
  intro K _ _ _ I _ φ hφ n M F hM hF
  classical
  obtain ⟨hd, hz⟩ := GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice K I φ hφ M hM
  haveI : Finite (𝓞 K ⧸ M) := Ideal.finiteQuotientOfFreeOfNeBot M hM
  letI : Fintype (𝓞 K ⧸ M) := Fintype.ofFinite _
  set L := lat φ M with hL
  set D := GlobalTheory.dualLattice L with hD
  have hI : Nonempty I := by
    obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
    obtain ⟨i, -, -⟩ := hφ σ
    exact ⟨i⟩
  have hinj : Function.Injective (embA φ) := by
    intro x x' h
    obtain ⟨i⟩ := hI
    have h2 := congrArg (fun z : EuclideanSpace ℂ I => z i) h
    simp only [embA_apply] at h2
    exact RingOfIntegers.ext ((φ i).injective h2)

  set u : 𝓞 K ⧸ M → EuclideanSpace ℂ I := fun c => embA φ (Quotient.out c) with hu
  set half : D → (I → ℂ) := fun l i => (l : EuclideanSpace ℂ I) i / 2 with hhalf_def
  have hhalf : Function.Injective half := by
    intro l l' h
    apply Subtype.ext
    ext i
    have := congrFun h i
    simp only [hhalf_def] at this
    linear_combination 2 * this
  set cov : ℂ := ((ZLattice.covolume L : ℝ) : ℂ) with hcov
  set A : D → ℂ := fun l => cov⁻¹ * ∑ c : 𝓞 K ⧸ M, F (Quotient.out c) *
    Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ)) with hA
  set a : (I → ℂ) → ℂ := fun v => if h : ∃ l : D, half l = v then A (Classical.choose h) else 0 with ha_def
  have ha_half : ∀ l, a (half l) = A l := by
    intro l
    have h : ∃ l' : D, half l' = half l := ⟨l, rfl⟩
    simp only [ha_def, dif_pos h]
    rw [hhalf (Classical.choose_spec h)]
  have ha_zero : ∀ v, v ∉ Set.range half → a v = 0 := by
    intro v hv
    have h : ¬ ∃ l : D, half l = v := fun ⟨l, hl⟩ => hv ⟨l, hl⟩
    simp only [ha_def, dif_neg h]
  set B : ℝ := ‖cov⁻¹‖ * ∑ c : 𝓞 K ⧸ M, ‖F (Quotient.out c)‖ with hB
  have hB0 : 0 ≤ B := by positivity
  have hAB : ∀ l, ‖A l‖ ≤ B := by
    intro l
    simp only [hA, hB, norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)) (norm_nonneg _)
    rw [norm_mul, GlobalTheory.norm_cexp_two_pi_I, mul_one]
  set cI : ℝ := (Fintype.card I : ℝ) with hcI
  have hcI0 : 0 ≤ cI := by positivity
  have hnorm : ∀ l : D, ‖(l : EuclideanSpace ℂ I)‖ ^ 2 ≤ (4 * cI + 1) * ‖half l‖ ^ 2 := by
    intro l
    have := norm_half_sq (l : EuclideanSpace ℂ I)
    nlinarith [sq_nonneg ‖half l‖]
  refine ⟨a, kappa n, ?_, ?_, ?_⟩
  ·
    intro ε hε
    have hpos : 0 < ε / (4 * cI + 1) := by positivity
    have key : Summable (fun l : D => ‖a (half l)‖ * Real.exp (-ε * ‖half l‖ ^ 2)) := by
      refine .of_nonneg_of_le (fun _ => by positivity) (fun l => ?_)
        ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq D hpos).mul_left B)
      rw [ha_half]
      refine mul_le_mul (hAB l) (Real.exp_le_exp.2 ?_) (by positivity) hB0
      have h1 := hnorm l
      have h2 : ε / (4 * cI + 1) * ‖(l : EuclideanSpace ℂ I)‖ ^ 2 ≤ ε * ‖half l‖ ^ 2 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
      linarith
    exact (hhalf.summable_iff (f := fun v => ‖a v‖ * Real.exp (-ε * ‖v‖ ^ 2))
      (fun v hv => by simp [ha_zero v hv])).1 key
  ·
    obtain ⟨r, hr, hr'⟩ := discrete_norm_ge (GlobalTheory.dualLattice L)
    refine ⟨r / (4 * cI + 1), by positivity, fun v hav hv0 => ?_⟩
    by_cases hv : v ∈ Set.range half
    · obtain ⟨l, rfl⟩ := hv
      have hl0 : l ≠ 0 := by
        rintro rfl
        apply hv0
        funext i
        simp [hhalf_def]
      have h1 : r ≤ ‖(l : EuclideanSpace ℂ I)‖ := hr' ⟨l, l.2⟩ (fun h => hl0 (Subtype.ext (congrArg Subtype.val h)))
      have h2 := hnorm l
      have h3 : r ^ 2 ≤ ((4 * cI + 1) * ‖half l‖) ^ 2 := by
        have : r ^ 2 ≤ ‖(l : EuclideanSpace ℂ I)‖ ^ 2 := pow_le_pow_left₀ hr.le h1 2
        have h4 : (4 * cI + 1) * ‖half l‖ ^ 2 ≤ ((4 * cI + 1) * ‖half l‖) ^ 2 := by
          rw [mul_pow]
          have : (4 * cI + 1) ≤ (4 * cI + 1) ^ 2 := by nlinarith
          exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
        linarith
      have h5 : r ≤ (4 * cI + 1) * ‖half l‖ := (pow_le_pow_iff_left₀ hr.le (by positivity) two_ne_zero).1 h3
      rw [div_le_iff₀ (by positivity)]
      linarith
    · exact absurd (ha_zero v hv) hav
  ·
    intro y
    obtain ⟨hd', hz'⟩ := GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice K I φ hφ ⊤ (by simp)
    obtain ⟨C, b, hC0, hb, hC⟩ := gauss_dil_bound n y
    set BF : ℝ := ∑ c : 𝓞 K ⧸ M, ‖F (Quotient.out c)‖ with hBF
    have hFc : ∀ α : 𝓞 K, F α = F (Quotient.out (Ideal.Quotient.mk M α)) := by
      intro α
      have hm : α - Quotient.out (Ideal.Quotient.mk M α) ∈ M := by
        rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
      have := hF (Quotient.out (Ideal.Quotient.mk M α)) _ hm
      rw [add_sub_cancel] at this
      exact this
    have hFB : ∀ α : 𝓞 K, ‖F α‖ ≤ BF := by
      intro α
      rw [hFc α]
      exact Finset.single_le_sum (f := fun c => ‖F (Quotient.out c)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)
    have hemb : ∀ α : 𝓞 K, emb φ (α : K) = WithLp.ofLp (embA φ α) := fun α => rfl
    have hsum : Summable (fun α : 𝓞 K => F α * gauss n (dil y (emb φ (α : K)))) := by
      have hT : Summable (fun x : lat φ ⊤ => BF * (C * Real.exp (-b * ‖(x : EuclideanSpace ℂ I)‖ ^ 2))) :=
        ((GlobalTheory.summable_lattice_exp_neg_mul_norm_sq (lat φ ⊤) hb).mul_left C).mul_left BF
      have hi : Function.Injective (fun α : 𝓞 K => (⟨embA φ α, mem_lat.2 ⟨α, Submodule.mem_top, rfl⟩⟩ : lat φ ⊤)) :=
        fun x x' h => hinj (congrArg Subtype.val h)
      refine Summable.of_norm_bounded (hT.comp_injective hi) (fun α => ?_)
      simp only [Function.comp_apply, norm_mul]
      exact mul_le_mul (hFB α) (hC (embA φ α)) (norm_nonneg _) (by positivity)

    let e : M ≃ L := Equiv.ofBijective (fun μ => (⟨embA φ μ, mem_lat.2 ⟨μ, μ.2, rfl⟩⟩ : L))
      ⟨fun x x' h => Subtype.ext (hinj (congrArg Subtype.val h)), fun x => by
        obtain ⟨μ, hμ, h⟩ := mem_lat.1 x.2
        exact ⟨⟨μ, hμ⟩, Subtype.ext h⟩⟩
    have hcoset : ∀ c : 𝓞 K ⧸ M, ∑' μ : M, F (Quotient.out c + μ) * gauss n (dil y (emb φ ((Quotient.out c + μ : 𝓞 K) : K))) =
        F (Quotient.out c) * (cov⁻¹ * ((Real.exp (-∑ i, y i) : ℂ) * kappa n) *
          ∑' l : D, Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ)) *
            gauss n (dil (-y) (half l))) := by
      intro c
      have h1 : ∀ μ : M, F (Quotient.out c + μ) * gauss n (dil y (emb φ ((Quotient.out c + μ : 𝓞 K) : K))) =
          F (Quotient.out c) * gauss n (dil y (WithLp.ofLp (((e μ : L) : EuclideanSpace ℂ I) + u c))) := by
        intro μ
        rw [hF _ _ μ.2]
        have hx : emb φ ((Quotient.out c + μ : 𝓞 K) : K) = WithLp.ofLp (((e μ : L) : EuclideanSpace ℂ I) + u c) := by
          funext i
          show φ i ((Quotient.out c + μ : 𝓞 K) : K) = (embA φ μ + embA φ (Quotient.out c)) i
          rw [PiLp.add_apply, embA_apply, embA_apply]
          push_cast
          rw [map_add, add_comm]
        rw [hx]
      rw [tsum_congr h1, tsum_mul_left,
        e.tsum_eq (fun x : L => gauss n (dil y (WithLp.ofLp ((x : EuclideanSpace ℂ I) + u c)))),
        (poisson_coset L n y (u c)).2]
    have hLHS := GlobalTheory.T.tsum_ring_eq_sum_ideal_cosets_tsum (𝓞 K) M _ hsum
    unfold GlobalTheory.HeckeTheta.theta
    rw [hLHS, Finset.sum_congr rfl (fun c _ => hcoset c)]

    have hsupp : Function.support (fun v : I → ℂ => a v * gauss n (dil (-y) v)) ⊆ Set.range half := by
      intro v hv
      by_contra h
      exact hv (by simp [ha_zero v h])
    rw [← hhalf.tsum_eq hsupp]
    simp only [ha_half, hA]
    have hsc : ∀ c ∈ (Finset.univ : Finset (𝓞 K ⧸ M)), Summable (fun l : D => cov⁻¹ * (F (Quotient.out c) *
        Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l))) := by
      intro c _
      refine Summable.of_norm_bounded (((poisson_coset L n y (u c)).1).mul_left (‖cov⁻¹‖ * ‖F (Quotient.out c)‖)) (fun l => ?_)
      rw [norm_mul, norm_mul, norm_mul, GlobalTheory.norm_cexp_two_pi_I, mul_one]
    have hre : ∀ l : D, cov⁻¹ * (∑ c : 𝓞 K ⧸ M, F (Quotient.out c) *
        Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l)) =
        ∑ c : 𝓞 K ⧸ M, cov⁻¹ * (F (Quotient.out c) *
        Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l)) := by
      intro l
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [tsum_congr hre, Summable.tsum_finsetSum hsc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hre2 : ∀ l : D, cov⁻¹ * (F (Quotient.out c) *
        Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ))) * gauss n (dil (-y) (half l)) =
        (cov⁻¹ * F (Quotient.out c)) * (Complex.exp (2 * Real.pi * Complex.I * ((⟪(l : EuclideanSpace ℂ I), u c⟫ : ℝ) : ℂ)) *
          gauss n (dil (-y) (half l))) := fun l => by ring
    rw [tsum_congr hre2, tsum_mul_left]
    ring

end GlobalTheory.HeckePoisson
