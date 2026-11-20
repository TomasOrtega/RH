import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.HessCRestrictThm
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartCutoffEnergy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergyCocycle
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartEnergySwap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace ChartIntegrationByPartsSymmetry

section Potentials

variable {e : ℕ}

/- English proof (translation)
Establish `hs : ContDiff ℝ m fun y : Fin D → ℂ => 1 + ∑ i, ‖y i‖ ^ 2` using `contDiff_const.add (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))`. Establish `hpos : ∀ y : Fin D → ℂ, 0 < 1 + ∑ i, ‖y i‖ ^ 2` using `fun y => by positivity`. Conclude with `(hs.sqrt fun y => (hpos y).ne').log fun y => (Real.sqrt_pos.mpr (hpos y)).ne'`.
-/
theorem contDiff_gbPot_of_le {D : ℕ} (m : ℕ) : ContDiff ℝ m (gbPot (D := D)) := by
  have hs : ContDiff ℝ m fun y : Fin D → ℂ => 1 + ∑ i, ‖y i‖ ^ 2 :=
    contDiff_const.add (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))
  have hpos : ∀ y : Fin D → ℂ, 0 < 1 + ∑ i, ‖y i‖ ^ 2 := fun y => by positivity
  exact (hs.sqrt fun y => (hpos y).ne').log fun y => (Real.sqrt_pos.mpr (hpos y)).ne'

/- English proof (translation)
Take `⟨c, P, κ, hP, hEq⟩` from `ChartDensityIntegrableAlt.hermChartPot_eq_gbPot_affine M hM`. Rewrite using `[hEq]`. Conclude with `((contDiff_gbPot_of_le m).comp (contDiff_const.add (ChartMongeAmpereAffineInvariance.realCLE P hP).contDiff)).add contDiff_const`.
-/
theorem contDiff_hermChartPot_of_le (m : ℕ) {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) :
    ContDiff ℝ m (hermChartPot M) := by
  obtain ⟨c, P, κ, hP, hEq⟩ := ChartDensityIntegrableAlt.hermChartPot_eq_gbPot_affine M hM
  rw [hEq]
  exact ((contDiff_gbPot_of_le m).comp
    (contDiff_const.add (ChartMongeAmpereAffineInvariance.realCLE P hP).contDiff)).add contDiff_const

/- English proof (translation)
Establish `key : star (star ξ) ⬝ᵥ (hessC φ z *ᵥ star ξ) = leviC (fderiv ℝ (fderiv ℝ φ) z) (star (star ξ)) (star (star ξ))`. Simplify using `only [dotProduct, mulVec, hessC_eq_leviC, sum_leviC_mul]`. Conclude with `sum_mul_leviC _ _ _`. Rewrite using `[key, star_star]`. Simplify using `[leviC, levi]`.
-/
theorem levi_eq_re (φ : (Fin e → ℂ) → ℝ) (z ξ : Fin e → ℂ) :
    levi φ z ξ = (star (star ξ) ⬝ᵥ (hessC φ z *ᵥ star ξ)).re := by
  have key : star (star ξ) ⬝ᵥ (hessC φ z *ᵥ star ξ) =
      leviC (fderiv ℝ (fderiv ℝ φ) z) (star (star ξ)) (star (star ξ)) := by
    simp only [dotProduct, mulVec, hessC_eq_leviC, sum_leviC_mul]
    exact sum_mul_leviC _ _ _
  rw [key, star_star]
  simp [leviC, levi]

/- English proof (translation)
Take `⟨C, hC⟩` from `ChartHessCompare.proof HermFormCompare.proof e M M hM hM`. Establish `hp : (hessC (hermChartPot M) z).PosSemidef` using `(hC z).1.posSemidef`. Rewrite using `[levi_eq_re]`. Conclude with `(Complex.nonneg_iff.mp (hp.dotProduct_mulVec_nonneg (star ξ))).1`.
-/
theorem levi_hermChartPot_nonneg {M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ} (hM : M.PosDef) (z ξ : Fin e → ℂ) :
    0 ≤ levi (hermChartPot M) z ξ := by
  obtain ⟨C, hC⟩ := ChartHessCompare.proof HermFormCompare.proof e M M hM hM
  have hp : (hessC (hermChartPot M) z).PosSemidef := (hC z).1.posSemidef
  rw [levi_eq_re]
  exact (Complex.nonneg_iff.mp (hp.dotProduct_mulVec_nonneg (star ξ))).1

end Potentials

section Cutoff

variable {D : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chartCutoff_apply (k : ℕ) (y : Fin D → ℂ) :
    chartCutoff k y = Real.smoothTransition (2 - (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2) := rfl

/- English proof (translation)
Establish `hs : ContDiff ℝ m fun y : Fin D → ℂ => ∑ i, ‖y i‖ ^ 2` using `ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i)`. Conclude with `Real.smoothTransition.contDiff.comp (contDiff_const.sub (hs.div_const _))`.
-/
theorem contDiff_chartCutoff (k : ℕ) (m : ℕ) : ContDiff ℝ m (chartCutoff (D := D) k) := by
  have hs : ContDiff ℝ m fun y : Fin D → ℂ => ∑ i, ‖y i‖ ^ 2 :=
    ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i)
  exact Real.smoothTransition.contDiff.comp (contDiff_const.sub (hs.div_const _))

/- English proof (translation)
The claim follows from `Real.smoothTransition.nonneg _`.
-/
theorem chartCutoff_nonneg (k : ℕ) (y : Fin D → ℂ) : 0 ≤ chartCutoff k y := Real.smoothTransition.nonneg _

/- English proof (translation)
The claim follows from `Real.smoothTransition.le_one _`.
-/
theorem chartCutoff_le_one (k : ℕ) (y : Fin D → ℂ) : chartCutoff k y ≤ 1 := Real.smoothTransition.le_one _

/- English proof (translation)
Apply `Real.smoothTransition.one_of_one_le` to reduce the goal to its premises. Establish `hk : (0 : ℝ) < ((k : ℝ) + 1) ^ 2` using `by positivity`. Establish `: (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2 ≤ 1` using `(div_le_one hk).mpr h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chartCutoff_eq_one {k : ℕ} {y : Fin D → ℂ} (h : ∑ i, ‖y i‖ ^ 2 ≤ ((k : ℝ) + 1) ^ 2) :
    chartCutoff k y = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hk : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have : (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2 ≤ 1 := (div_le_one hk).mpr h
  linarith

/- English proof (translation)
Apply `Real.smoothTransition.zero_of_nonpos` to reduce the goal to its premises. Establish `hk : (0 : ℝ) < ((k : ℝ) + 1) ^ 2` using `by positivity`. Establish `: 2 ≤ (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2` using `(le_div_iff₀ hk).mpr h`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chartCutoff_eq_zero {k : ℕ} {y : Fin D → ℂ} (h : 2 * ((k : ℝ) + 1) ^ 2 ≤ ∑ i, ‖y i‖ ^ 2) :
    chartCutoff k y = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  have hk : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have : 2 ≤ (∑ i, ‖y i‖ ^ 2) / ((k : ℝ) + 1) ^ 2 := (le_div_iff₀ hk).mpr h
  linarith

/- English proof (translation)
Introduce `a b hab`. Simplify using `only [chartCutoff_apply]`. Apply `Real.smoothTransition.monotone` to reduce the goal to its premises. Establish `hab' : ((a : ℝ) + 1) ^ 2 ≤ ((b : ℝ) + 1) ^ 2`. Establish `: (a : ℝ) ≤ b` using `by exact_mod_cast hab`.

Use `gcongr`. Establish `hs : 0 ≤ ∑ i, ‖y i‖ ^ 2` using `by positivity`. Use `div_le_div_of_nonneg_left hs (by positivity) hab'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem chartCutoff_mono (y : Fin D → ℂ) : Monotone fun k : ℕ => chartCutoff k y := by
  intro a b hab
  simp only [chartCutoff_apply]
  apply Real.smoothTransition.monotone
  have hab' : ((a : ℝ) + 1) ^ 2 ≤ ((b : ℝ) + 1) ^ 2 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    gcongr
  have hs : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
  have := div_le_div_of_nonneg_left hs (by positivity) hab'
  linarith

/- English proof (translation)
Take `⟨N, hN⟩` from `exists_nat_ge (Real.sqrt (∑ i, ‖y i‖ ^ 2))`. Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ge_atTop N] with k hk`. Use `symm`. Apply `chartCutoff_eq_one` to reduce the goal to its premises.

Establish `h0 : 0 ≤ ∑ i, ‖y i‖ ^ 2` using `by positivity`. Establish `hs : Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ (k : ℝ) + 1`. Establish `: (N : ℝ) ≤ k` using `by exact_mod_cast hk`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tendsto_chartCutoff (y : Fin D → ℂ) : Tendsto (fun k : ℕ => chartCutoff k y) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.sqrt (∑ i, ‖y i‖ ^ 2))
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with k hk
  symm
  apply chartCutoff_eq_one
  have h0 : 0 ≤ ∑ i, ‖y i‖ ^ 2 := by positivity
  have hs : Real.sqrt (∑ i, ‖y i‖ ^ 2) ≤ (k : ℝ) + 1 := by
    have : (N : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  calc ∑ i, ‖y i‖ ^ 2 = Real.sqrt (∑ i, ‖y i‖ ^ 2) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ ((k : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2

/- English proof (translation)
Use `HasCompactSupport.intro (isCompact_closedBall (0 : Fin D → ℂ) (2 * ((k : ℝ) + 1))) fun y hy => ?_` and prove the remaining obligations. Apply `chartCutoff_eq_zero` to reduce the goal to its premises. Establish `hr : (0 : ℝ) ≤ 2 * ((k : ℝ) + 1)` using `by positivity`. Rewrite `hy` using `[Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr]`. Simplify using `only [not_forall, not_le] at hy`.

Take `⟨i, hi⟩` from `hy`. Establish `h1 : ‖y i‖ ^ 2 ≤ ∑ j, ‖y j‖ ^ 2` using `Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)`. Establish `h2 : (2 * ((k : ℝ) + 1)) ^ 2 ≤ ‖y i‖ ^ 2` using `pow_le_pow_left₀ hr hi.le 2`. Use polynomial arithmetic with `[sq_nonneg ((k : ℝ) + 1)]`.
-/
theorem hasCompactSupport_chartCutoff (k : ℕ) : HasCompactSupport (chartCutoff (D := D) k) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin D → ℂ) (2 * ((k : ℝ) + 1))) fun y hy => ?_
  apply chartCutoff_eq_zero
  have hr : (0 : ℝ) ≤ 2 * ((k : ℝ) + 1) := by positivity
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr] at hy
  simp only [not_forall, not_le] at hy
  obtain ⟨i, hi⟩ := hy
  have h1 : ‖y i‖ ^ 2 ≤ ∑ j, ‖y j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖y j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  have h2 : (2 * ((k : ℝ) + 1)) ^ 2 ≤ ‖y i‖ ^ 2 := pow_le_pow_left₀ hr hi.le 2
  nlinarith [sq_nonneg ((k : ℝ) + 1)]

/- English proof (translation)
Establish `hc : Continuous fun z : Fin D → ℂ => ∑ i, ‖z i‖ ^ 2` using `by fun_prop`. Establish `hopen : IsOpen {z : Fin D → ℂ | ∑ i, ‖z i‖ ^ 2 < ((k : ℝ) + 1) ^ 2}` using `isOpen_lt hc continuous_const`. Establish `hev : chartCutoff k =ᶠ[𝓝 y] fun _ => (1 : ℝ)` using `by filter_upwards [hopen.mem_nhds h] with z hz`. Conclude with `chartCutoff_eq_one (le_of_lt hz)`. Rewrite using `[hev.fderiv_eq]`.

Simplify using the standard rewrite rules.
-/
theorem fderiv_chartCutoff_eq_zero {k : ℕ} {y : Fin D → ℂ} (h : ∑ i, ‖y i‖ ^ 2 < ((k : ℝ) + 1) ^ 2) :
    fderiv ℝ (chartCutoff k) y = 0 := by
  have hc : Continuous fun z : Fin D → ℂ => ∑ i, ‖z i‖ ^ 2 := by fun_prop
  have hopen : IsOpen {z : Fin D → ℂ | ∑ i, ‖z i‖ ^ 2 < ((k : ℝ) + 1) ^ 2} := isOpen_lt hc continuous_const
  have hev : chartCutoff k =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [hopen.mem_nhds h] with z hz
    exact chartCutoff_eq_one (le_of_lt hz)
  rw [hev.fderiv_eq]
  simp

end Cutoff

section GradDens

variable {D : ℕ}

/- English proof (translation)
Use extensionality with `j k`. Simplify using `[gradMat, dz_cplx, h]`.
-/
theorem gradMat_eq_zero_left {v w : (Fin D → ℂ) → ℝ} {z : Fin D → ℂ} (h : fderiv ℝ v z = 0) :
    gradMat v w z = 0 := by
  ext j k
  simp [gradMat, dz_cplx, h]

/- English proof (translation)
Establish `h0` using `mdisc_cons_smul_fst (0 : ℂ) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) fun i => hessC (φ i) z`. Simplify using `only [smul_zero, zero_mul] at h0`. Simplify using `[gradDens, h, h0]`.
-/
theorem gradDens_eq_zero_of_gradMat {n : ℕ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} {v w : (Fin (n + 1) → ℂ) → ℝ}
    {z : Fin (n + 1) → ℂ} (h : gradMat v w z = 0) : gradDens φ v w z = 0 := by
  have h0 := mdisc_cons_smul_fst (0 : ℂ) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) fun i => hessC (φ i) z
  simp only [smul_zero, zero_mul] at h0
  simp [gradDens, h, h0]

/- English proof (translation)
The claim follows from `gradDens_eq_zero_of_gradMat (gradMat_eq_zero_left (fderiv_chartCutoff_eq_zero h))`.
-/
theorem gradDens_chartCutoff_left {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (w : (Fin (n + 1) → ℂ) → ℝ)
    {k : ℕ} {y : Fin (n + 1) → ℂ} (h : ∑ i, ‖y i‖ ^ 2 < ((k : ℝ) + 1) ^ 2) :
    gradDens φ (chartCutoff k) w y = 0 :=
  gradDens_eq_zero_of_gradMat (gradMat_eq_zero_left (fderiv_chartCutoff_eq_zero h))

/- English proof (translation)
Unfold `mdisc`. Use `continuous_const.mul (continuous_finsetSum _ fun S _ => continuous_const.mul ?_)` and prove the remaining obligations. Conclude with `(continuous_finsetSum _ fun k _ => hF k).matrix_det`.
-/
theorem continuous_mdisc {X : Type*} [TopologicalSpace X] {F : X → Fin D → Matrix (Fin D) (Fin D) ℂ}
    (hF : ∀ k, Continuous fun x => F x k) : Continuous fun x => mdisc (F x) := by
  unfold mdisc
  refine continuous_const.mul (continuous_finsetSum _ fun S _ => continuous_const.mul ?_)
  exact (continuous_finsetSum _ fun k _ => hF k).matrix_det

/- English proof (translation)
Establish `h1 : Continuous (fderiv ℝ (fderiv ℝ φ))` using `(hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero`. Establish `hH : ∀ a b : Fin D → ℂ, Continuous fun z => fderiv ℝ (fderiv ℝ φ) z a b` using `fun a b => (h1.clm_apply continuous_const).clm_apply continuous_const`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Conclude with `((Complex.continuous_ofReal.comp ((hH _ _).add (hH _ _))).add (continuous_const.mul (Complex.continuous_ofReal.comp ((hH _ _).sub (hH _ _))))).div_const _`.
-/
theorem continuous_hessC {φ : (Fin D → ℂ) → ℝ} (hφ : ContDiff ℝ 2 φ) : Continuous (hessC φ) := by
  have h1 : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hH : ∀ a b : Fin D → ℂ, Continuous fun z => fderiv ℝ (fderiv ℝ φ) z a b := fun a b =>
    (h1.clm_apply continuous_const).clm_apply continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact ((Complex.continuous_ofReal.comp ((hH _ _).add (hH _ _))).add
    (continuous_const.mul (Complex.continuous_ofReal.comp ((hH _ _).sub (hH _ _))))).div_const _

/- English proof (translation)
Establish `hv' : ∀ a, Continuous fun z => fderiv ℝ v z a` using `fun a => (hv.continuous_fderiv one_ne_zero).clm_apply continuous_const`. Establish `hw' : ∀ a, Continuous fun z => fderiv ℝ w z a` using `fun a => (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const`. Use `continuous_pi fun j => continuous_pi fun k => ?_` and prove the remaining obligations. Simplify using `only [gradMat, dz_cplx, dzb_cplx]`. Conclude with `(((Complex.continuous_ofReal.comp (hv' _)).sub (continuous_const.mul (Complex.continuous_ofReal.comp (hv' _)))).div_const 2).mul (((Complex.continuous_ofReal.comp (hw' _)).add (continuous_const.mul (Complex.continuous_ofReal.comp (hw' _)))).div_const 2)`.
-/
theorem continuous_gradMat {v w : (Fin D → ℂ) → ℝ} (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w) :
    Continuous (gradMat v w) := by
  have hv' : ∀ a, Continuous fun z => fderiv ℝ v z a := fun a =>
    (hv.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hw' : ∀ a, Continuous fun z => fderiv ℝ w z a := fun a =>
    (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine continuous_pi fun j => continuous_pi fun k => ?_
  simp only [gradMat, dz_cplx, dzb_cplx]
  exact (((Complex.continuous_ofReal.comp (hv' _)).sub
      (continuous_const.mul (Complex.continuous_ofReal.comp (hv' _)))).div_const 2).mul
    (((Complex.continuous_ofReal.comp (hw' _)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp (hw' _)))).div_const 2)

/- English proof (translation)
Unfold `gradDens`. Use `continuous_const.mul (Complex.continuous_re.comp (continuous_mdisc fun k => ?_))` and prove the remaining obligations. Use `Fin.cases ?_ (fun i => ?_) k` and prove the remaining obligations. Simplify using `using continuous_gradMat hv hw`. Simplify using `using continuous_hessC (hφ i)`.
-/
theorem continuous_gradDens {n : ℕ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ i, ContDiff ℝ 2 (φ i))
    {v w : (Fin (n + 1) → ℂ) → ℝ} (hv : ContDiff ℝ 1 v) (hw : ContDiff ℝ 1 w) :
    Continuous (gradDens φ v w) := by
  unfold gradDens
  refine continuous_const.mul (Complex.continuous_re.comp (continuous_mdisc fun k => ?_))
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using continuous_gradMat hv hw
  · simpa using continuous_hessC (hφ i)

/- English proof (translation)
Use `(hv.fderiv (𝕜 := ℝ)).mono fun z hz => ?_` and prove the remaining obligations. Rewrite `hz`, the goal using `[Function.mem_support]`. Conclude with `fun h0 => hz (gradDens_eq_zero_of_gradMat (gradMat_eq_zero_left h0))`.
-/
theorem hasCompactSupport_gradDens_left {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ)
    {v : (Fin (n + 1) → ℂ) → ℝ} (w : (Fin (n + 1) → ℂ) → ℝ) (hv : HasCompactSupport v) :
    HasCompactSupport (gradDens φ v w) := by
  refine (hv.fderiv (𝕜 := ℝ)).mono fun z hz => ?_
  rw [Function.mem_support] at hz ⊢
  exact fun h0 => hz (gradDens_eq_zero_of_gradMat (gradMat_eq_zero_left h0))

/- English proof (translation)
Establish `hv : ContDiff ℝ 3 (fun y => ψ y * u y)` using `hψ.mul hu`. Establish `hvc : HasCompactSupport (fun y => ψ y * u y)` using `hψc.mul_right`. Establish `hyp : PartsHyp φ (fun y => ψ y * u y) w Set.univ` using `⟨isOpen_univ, hv.contDiffOn, hvc, Set.subset_univ _, hw.contDiffOn, fun i => (hφ i).contDiffOn⟩`. Take `⟨h1, -, -, h4, -⟩` from `parts_thm n φ _ w Set.univ hyp`. Establish `h21 : ∀ i, ContDiff ℝ 2 (φ i)` using `fun i => (hφ i).of_le (by norm_num)`.

Establish `hone : ((1 : ℕ) : WithTop ℕ∞) ≤ 3` using `by norm_num`. Establish `hg1 : Integrable (fun y => ψ y * gradDens φ u w y)` using `(hψ.continuous.mul (continuous_gradDens h21 (hu.of_le hone) (hw.of_le hone))).integrable_of_hasCompactSupport hψc.mul_right`. Establish `hg2 : Integrable (fun y => u y * gradDens φ ψ w y)` using `(hu.continuous.mul (continuous_gradDens h21 (hψ.of_le hone) (hw.of_le hone))).integrable_of_hasCompactSupport (hasCompactSupport_gradDens_left φ w hψc).mul_left`. Use `⟨?_, hg1, hg2, ?_⟩` and prove the remaining obligations. Simplify `h1` using `[IntegrableOn, Measure.restrict_univ]`.

Establish `hL : ∀ y, gradDens φ (fun y => ψ y * u y) w y = ψ y * gradDens φ u w y + u y * gradDens φ ψ w y` using `fun y => (gradDensLeibniz_thm n φ ψ u w y (hψ.differentiable (by norm_num) y) (hu.differentiable (by norm_num) y)).1`. Establish `h4' : ∫ y, ψ y * u y * maDens (Fin.cons w φ) y = -∫ y, gradDens φ (fun y => ψ y * u y) w y`. Simplify `h4` using `[maInt, gradInt, Measure.restrict_univ]`. Rewrite using `[h4']`. Repeatedly rewrite using `[hL]`.

Rewrite using `[integral_add hg1 hg2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem parts_cutoff {n : ℕ} {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} (hφ : ∀ i, ContDiff ℝ 3 (φ i))
    {ψ u w : (Fin (n + 1) → ℂ) → ℝ} (hψ : ContDiff ℝ 3 ψ) (hψc : HasCompactSupport ψ)
    (hu : ContDiff ℝ 3 u) (hw : ContDiff ℝ 3 w) :
    Integrable (fun y => ψ y * u y * maDens (Fin.cons w φ) y) ∧
      Integrable (fun y => ψ y * gradDens φ u w y) ∧
      Integrable (fun y => u y * gradDens φ ψ w y) ∧
      ∫ y, ψ y * u y * maDens (Fin.cons w φ) y =
        -(∫ y, ψ y * gradDens φ u w y) - ∫ y, u y * gradDens φ ψ w y := by
  have hv : ContDiff ℝ 3 (fun y => ψ y * u y) := hψ.mul hu
  have hvc : HasCompactSupport (fun y => ψ y * u y) := hψc.mul_right
  have hyp : PartsHyp φ (fun y => ψ y * u y) w Set.univ :=
    ⟨isOpen_univ, hv.contDiffOn, hvc, Set.subset_univ _, hw.contDiffOn, fun i => (hφ i).contDiffOn⟩
  obtain ⟨h1, -, -, h4, -⟩ := parts_thm n φ _ w Set.univ hyp
  have h21 : ∀ i, ContDiff ℝ 2 (φ i) := fun i => (hφ i).of_le (by norm_num)
  have hone : ((1 : ℕ) : WithTop ℕ∞) ≤ 3 := by norm_num
  have hg1 : Integrable (fun y => ψ y * gradDens φ u w y) :=
    (hψ.continuous.mul (continuous_gradDens h21 (hu.of_le hone) (hw.of_le hone))).integrable_of_hasCompactSupport
      hψc.mul_right
  have hg2 : Integrable (fun y => u y * gradDens φ ψ w y) :=
    (hu.continuous.mul (continuous_gradDens h21 (hψ.of_le hone) (hw.of_le hone))).integrable_of_hasCompactSupport
      (hasCompactSupport_gradDens_left φ w hψc).mul_left
  refine ⟨?_, hg1, hg2, ?_⟩
  · simpa [IntegrableOn, Measure.restrict_univ] using h1
  · have hL : ∀ y, gradDens φ (fun y => ψ y * u y) w y = ψ y * gradDens φ u w y + u y * gradDens φ ψ w y :=
      fun y => (gradDensLeibniz_thm n φ ψ u w y (hψ.differentiable (by norm_num) y)
        (hu.differentiable (by norm_num) y)).1
    have h4' : ∫ y, ψ y * u y * maDens (Fin.cons w φ) y = -∫ y, gradDens φ (fun y => ψ y * u y) w y := by
      simpa [maInt, gradInt, Measure.restrict_univ] using h4
    rw [h4']
    simp_rw [hL]
    rw [integral_add hg1 hg2]
    ring

end GradDens

section Chart

variable {n : ℕ}

/- English proof (translation)
The claim follows from `gradDensSymm_thm n _ v w Set.univ isOpen_univ (fun i => (contDiff_hermChartPot_of_le 2 (hT i)).contDiffOn) y (Set.mem_univ _)`.
-/
theorem gradDens_chart_comm {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    (v w : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) :
    gradDens (fun i => hermChartPot (T i)) v w y = gradDens (fun i => hermChartPot (T i)) w v y :=
  gradDensSymm_thm n _ v w Set.univ isOpen_univ (fun i => (contDiff_hermChartPot_of_le 2 (hT i)).contDiffOn) y
    (Set.mem_univ _)

/- English proof (translation)
The claim follows from `gradDensNonneg_thm n _ v Set.univ isOpen_univ (fun i => (contDiff_hermChartPot_of_le 2 (hT i)).contDiffOn) (fun i z _ ξ => levi_hermChartPot_nonneg (hT i) z ξ) y (Set.mem_univ _)`.
-/
theorem gradDens_chart_nonneg {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    (v : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) :
    0 ≤ gradDens (fun i => hermChartPot (T i)) v v y :=
  gradDensNonneg_thm n _ v Set.univ isOpen_univ (fun i => (contDiff_hermChartPot_of_le 2 (hT i)).contDiffOn)
    (fun i z _ ξ => levi_hermChartPot_nonneg (hT i) z ξ) y (Set.mem_univ _)

/- English proof (translation)
The claim follows from `|gradDens (fun i => hermChartPot (T i)) v w y| ≤ Real.sqrt (gradDens (fun i => hermChartPot (T i)) v v y) * Real.sqrt (gradDens (fun i => hermChartPot (T i)) w w y) := by have hcs := gradDensCauchySchwarz_thm n (fun i => hermChartPot (T i)) v w Set.univ isOpen_univ (fun i => (con …`.
-/
theorem abs_gradDens_chart_le {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hT : ∀ i, (T i).PosDef)
    (v w : (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) :
    |gradDens (fun i => hermChartPot (T i)) v w y| ≤
      Real.sqrt (gradDens (fun i => hermChartPot (T i)) v v y) *
        Real.sqrt (gradDens (fun i => hermChartPot (T i)) w w y) := by
  have hcs := gradDensCauchySchwarz_thm n (fun i => hermChartPot (T i)) v w Set.univ isOpen_univ
    (fun i => (contDiff_hermChartPot_of_le 2 (hT i)).contDiffOn)
    (fun i z _ ξ => levi_hermChartPot_nonneg (hT i) z ξ) y (Set.mem_univ _)
  rw [← Real.sqrt_mul (gradDens_chart_nonneg hT v y)]
  exact Real.abs_le_sqrt hcs

/- English proof (translation)
Use function extensionality and compare the values at `j`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) j <;> simp`.
-/
theorem cons_hermChartPot (C : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) :
    (fun j => hermChartPot ((Fin.cons C T : Fin (n + 1) → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) j)) =
      (Fin.cons (hermChartPot C) fun i => hermChartPot (T i) : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> simp

/- English proof (translation)
Establish `h1 : fderiv ℝ (fun y => f y - g y) = fun y => fderiv ℝ f y - fderiv ℝ g y`. Use function extensionality and compare the values at `y`. Conclude with `fderiv_sub (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)`. Establish `hf1 : Differentiable ℝ (fderiv ℝ f)` using `(hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero`. Establish `hg1 : Differentiable ℝ (fderiv ℝ g)` using `(hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero`.

Establish `h2 : fderiv ℝ (fderiv ℝ fun y => f y - g y) z = fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ g) z`. Rewrite using `[h1]`. Conclude with `fderiv_sub (hf1 z) (hg1 z)`. Use extensionality with `i j`. Simplify using `only [hessC, h2, _root_.sub_apply, Matrix.sub_apply]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hessC_sub {D : ℕ} {f g : (Fin D → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (z : Fin D → ℂ) :
    hessC (fun y => f y - g y) z = hessC f z - hessC g z := by
  have h1 : fderiv ℝ (fun y => f y - g y) = fun y => fderiv ℝ f y - fderiv ℝ g y := by
    funext y
    exact fderiv_sub (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)
  have hf1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hg1 : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have h2 : fderiv ℝ (fderiv ℝ fun y => f y - g y) z = fderiv ℝ (fderiv ℝ f) z - fderiv ℝ (fderiv ℝ g) z := by
    rw [h1]
    exact fderiv_sub (hf1 z) (hg1 z)
  ext i j
  simp only [hessC, h2, _root_.sub_apply, Matrix.sub_apply]
  push_cast
  ring

/- English proof (translation)
Establish `hcons : ∀ h : (Fin (n + 1) → ℂ) → ℝ, (fun k => hessC ((Fin.cons h φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z) = (Fin.cons (hessC h z) fun i => hessC (φ i) z : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)`. Introduce `h`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `refine Fin.cases ?_ (fun i => ?_) k <;> simp`. Establish `hsub : hessC (fun y => f y - g y) z = (1 : ℂ) • hessC f z + (-1 : ℂ) • hessC g z`.

Rewrite using `[hessC_sub hf hg z]`. Simplify using `[sub_eq_add_neg]`. Establish `key` using `mdisc_cons_smul_add (1 : ℂ) (-1) (hessC f z) (hessC g z) fun i => hessC (φ i) z`. Express the relevant statement in the definitionally equal form `((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) * (mdisc fun k => hessC ((Fin.cons (fun y => f y - g y) φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z).re = ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) * (mdisc fun k => hessC ((Fin.cons f φ : Fin (n + 1) → (Fin (n + 1) → ℂ) …`. Rewrite using `[hcons, hcons, hcons, hsub, key]`.

Simplify using `only [one_mul, neg_one_mul, Complex.add_re, Complex.neg_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem maDensity_cons_sub {f g : (Fin (n + 1) → ℂ) → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ) :
    maDensity (Fin.cons (fun y => f y - g y) φ) z = maDensity (Fin.cons f φ) z - maDensity (Fin.cons g φ) z := by
  have hcons : ∀ h : (Fin (n + 1) → ℂ) → ℝ,
      (fun k => hessC ((Fin.cons h φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z) =
        (Fin.cons (hessC h z) fun i => hessC (φ i) z : Fin (n + 1) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
    intro h
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  have hsub : hessC (fun y => f y - g y) z = (1 : ℂ) • hessC f z + (-1 : ℂ) • hessC g z := by
    rw [hessC_sub hf hg z]
    simp [sub_eq_add_neg]
  have key := mdisc_cons_smul_add (1 : ℂ) (-1) (hessC f z) (hessC g z) fun i => hessC (φ i) z
  change ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
      (mdisc fun k => hessC ((Fin.cons (fun y => f y - g y) φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z).re =
    ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
        (mdisc fun k => hessC ((Fin.cons f φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z).re -
      ((n + 1).factorial : ℝ) * (2 / Real.pi) ^ (n + 1) *
        (mdisc fun k => hessC ((Fin.cons g φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) z).re
  rw [hcons, hcons, hcons, hsub, key]
  simp only [one_mul, neg_one_mul, Complex.add_re, Complex.neg_re]
  ring

/- English proof (translation)
Establish `hs : ∀ X : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ, X.PosDef → ∀ j, ((Fin.cons X T : Fin (n + 1) → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) j).PosDef`. Introduce `X hX j`. Use `Fin.cases ?_ (fun i => ?_) j` and prove the remaining obligations. Simplify using `using hX`. Simplify using `using hT i`.

Establish `h1` using `ChartEnergyCocycleAlt.integrable_pairing hA hB (hs C hC)`. Establish `h2` using `ChartEnergyCocycleAlt.integrable_pairing hA hB (hs D hD)`. Use `(h1.sub h2).congr (Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [ChartEnergyCocycleAlt.dens, cons_hermChartPot]`. Rewrite using `[maDensity_cons_sub (contDiff_hermChartPot_of_le 2 hC) (contDiff_hermChartPot_of_le 2 hD)]`.

Simplify using `only [Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integrable_pot_mul_maDensity {A B C D : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ}
    {T : Fin n → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ} (hA : A.PosDef) (hB : B.PosDef) (hC : C.PosDef)
    (hD : D.PosDef) (hT : ∀ i, (T i).PosDef) :
    Integrable (fun y : Fin (n + 1) → ℂ => (hermChartPot A y - hermChartPot B y) *
      maDensity (Fin.cons (fun y' => hermChartPot C y' - hermChartPot D y') fun i => hermChartPot (T i)) y) := by
  have hs : ∀ X : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ, X.PosDef →
      ∀ j, ((Fin.cons X T : Fin (n + 1) → Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) j).PosDef := by
    intro X hX j
    refine Fin.cases ?_ (fun i => ?_) j
    · simpa using hX
    · simpa using hT i
  have h1 := ChartEnergyCocycleAlt.integrable_pairing hA hB (hs C hC)
  have h2 := ChartEnergyCocycleAlt.integrable_pairing hA hB (hs D hD)
  refine (h1.sub h2).congr (Eventually.of_forall fun y => ?_)
  simp only [ChartEnergyCocycleAlt.dens, cons_hermChartPot]
  rw [maDensity_cons_sub (contDiff_hermChartPot_of_le 2 hC) (contDiff_hermChartPot_of_le 2 hD)]
  simp only [Pi.sub_apply]
  ring

end Chart

end ChartIntegrationByPartsSymmetry

end

end GroundTheory.Heights₂.Heights
