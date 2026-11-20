import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergySwap
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ChartHessHolo
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PChartDensityIntegrable
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Matrix MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace ChartEnergySwapHessian

open ChartMongeAmpereAffineInvariance

variable {e : ℕ}

def chartInv (y : Fin (e + 1) → ℂ) : Fin (e + 1) → ℂ := fun j => (y 0)⁻¹ * (if j = 0 then 1 else y j)

/- English proof (translation)
Simplify using `[chartInv]`.
-/
theorem chartInv_zero (y : Fin (e + 1) → ℂ) : chartInv y 0 = (y 0)⁻¹ := by
  simp [chartInv]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = 0`. Substitute `hj` using the available equality. Simplify using `[chartInv]`. Simplify using `only [chartInv, hj, if_false, if_true]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem chartInv_chartInv {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : chartInv (chartInv y) = y := by
  funext j
  by_cases hj : j = 0
  · subst hj
    simp [chartInv]
  · simp only [chartInv, hj, if_false, if_true]
    field_simp

/- English proof (translation)
Use function extensionality and compare the values at `p`. Rewrite using `[swapFirstTwo, PEquiv.toMatrix_toPEquiv_mulVec]`. Use `Fin.cases ?_ (fun i => ?_) p` and prove the remaining obligations. Simplify using the standard rewrite rules. Use `Fin.cases ?_ (fun k => ?_) i` and prove the remaining obligations.

Simplify using `[chartInv, hy]`. Establish `h0 : (k.succ.succ : Fin (e + 1 + 1)) ≠ 0` using `Fin.succ_ne_zero _`. Establish `h1 : (k.succ.succ : Fin (e + 1 + 1)) ≠ 1`. Rewrite using `[← Fin.succ_zero_eq_one, Ne, Fin.succ_inj]`. Conclude with `Fin.succ_ne_zero _`.

Simplify using `only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0 h1, Fin.cons_succ, Pi.smul_apply, smul_eq_mul, chartInv, Fin.succ_ne_zero, if_false]`. Clear the denominators using the available nonvanishing facts.
-/
theorem swap_mulVec_cons (y : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) :
    swapFirstTwo e *ᵥ (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ) =
      y 0 • (Fin.cons 1 (chartInv y) : Fin (e + 1 + 1) → ℂ) := by
  funext p
  rw [swapFirstTwo, PEquiv.toMatrix_toPEquiv_mulVec]
  refine Fin.cases ?_ (fun i => ?_) p
  · simp
  · refine Fin.cases ?_ (fun k => ?_) i
    · simp [chartInv, hy]
    · have h0 : (k.succ.succ : Fin (e + 1 + 1)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (k.succ.succ : Fin (e + 1 + 1)) ≠ 1 := by
        rw [← Fin.succ_zero_eq_one, Ne, Fin.succ_inj]
        exact Fin.succ_ne_zero _
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne h0 h1, Fin.cons_succ, Pi.smul_apply,
        smul_eq_mul, chartInv, Fin.succ_ne_zero, if_false]
      field_simp

/- English proof (translation)
Use `set u : Fin (e + 1 + 1) → ℂ := Fin.cons 1 (chartInv y) with hu`. Establish `hTv` using `swap_mulVec_cons y hy`. Establish `hq : star (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ) ⬝ᵥ (((swapFirstTwo e)ᴴ * M * swapFirstTwo e) *ᵥ (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ)) = (Complex.normSq (y 0) : ℂ) * (star u ⬝ᵥ (M *ᵥ u))`. Rewrite using `[← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hTv, star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.normSq_eq_conj_mul_self, starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hu0 : u ≠ 0` using `fun h => by`. Use `congrFun h 0` as an intermediate fact. Simplify using `[u] at this`. Establish `hx : 0 < (star u ⬝ᵥ (M *ᵥ u)).re` using `(Complex.pos_iff.mp (hM.dotProduct_mulVec_pos hu0)).1`. Simplify using `only [hermChartPot]`.

Rewrite using `[hq, Complex.re_ofReal_mul, Real.sqrt_mul (Complex.normSq_nonneg (y 0)), ← Complex.norm_def, Real.log_mul (norm_ne_zero_iff.mpr hy) (Real.sqrt_pos.mpr hx).ne']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermChartPot_swap (M : Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (hM : M.PosDef)
    (y : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) :
    hermChartPot ((swapFirstTwo e)ᴴ * M * swapFirstTwo e) y = hermChartPot M (chartInv y) + Real.log ‖y 0‖ := by
  set u : Fin (e + 1 + 1) → ℂ := Fin.cons 1 (chartInv y) with hu
  have hTv := swap_mulVec_cons y hy
  have hq : star (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ) ⬝ᵥ
      (((swapFirstTwo e)ᴴ * M * swapFirstTwo e) *ᵥ (Fin.cons 1 y : Fin (e + 1 + 1) → ℂ)) =
      (Complex.normSq (y 0) : ℂ) * (star u ⬝ᵥ (M *ᵥ u)) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec, hTv, star_smul, mulVec_smul,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.normSq_eq_conj_mul_self,
      starRingEnd_apply]
    ring
  have hu0 : u ≠ 0 := fun h => by
    have := congrFun h 0
    simp [u] at this
  have hx : 0 < (star u ⬝ᵥ (M *ᵥ u)).re := (Complex.pos_iff.mp (hM.dotProduct_mulVec_pos hu0)).1
  simp only [hermChartPot]
  rw [hq, Complex.re_ofReal_mul, Real.sqrt_mul (Complex.normSq_nonneg (y 0)), ← Complex.norm_def,
    Real.log_mul (norm_ne_zero_iff.mpr hy) (Real.sqrt_pos.mpr hx).ne']
  ring

/- English proof (translation)
Establish `hs : ContDiff ℝ 2 fun y : Fin D → ℂ => 1 + ∑ i, ‖y i‖ ^ 2` using `contDiff_const.add (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))`. Establish `hpos : ∀ y : Fin D → ℂ, 0 < 1 + ∑ i, ‖y i‖ ^ 2` using `fun y => by positivity`. Conclude with `(hs.sqrt fun y => (hpos y).ne').log fun y => (Real.sqrt_pos.mpr (hpos y)).ne'`.
-/
theorem contDiff_gbPot {D : ℕ} : ContDiff ℝ 2 (gbPot (D := D)) := by
  have hs : ContDiff ℝ 2 fun y : Fin D → ℂ => 1 + ∑ i, ‖y i‖ ^ 2 :=
    contDiff_const.add (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ i))
  have hpos : ∀ y : Fin D → ℂ, 0 < 1 + ∑ i, ‖y i‖ ^ 2 := fun y => by positivity
  exact (hs.sqrt fun y => (hpos y).ne').log fun y => (Real.sqrt_pos.mpr (hpos y)).ne'

/- English proof (translation)
Take `⟨c, P, κ, hP, hEq⟩` from `ChartDensityIntegrableAlt.hermChartPot_eq_gbPot_affine M hM`. Rewrite using `[hEq]`. Conclude with `(contDiff_gbPot.comp (contDiff_const.add (realCLE P hP).contDiff)).add contDiff_const`.
-/
theorem contDiff_hermChartPot (M : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (hM : M.PosDef) :
    ContDiff ℝ 2 (hermChartPot M) := by
  obtain ⟨c, P, κ, hP, hEq⟩ := ChartDensityIntegrableAlt.hermChartPot_eq_gbPot_affine M hM
  rw [hEq]
  exact (contDiff_gbPot.comp (contDiff_const.add (realCLE P hP).contDiff)).add contDiff_const

/- English proof (translation)
Establish `h0 : ContDiffAt ℂ 2 (fun y : Fin (e + 1) → ℂ => (y 0)⁻¹) y` using `(contDiff_apply ℂ ℂ (0 : Fin (e + 1))).contDiffAt.inv hy`. Use `contDiffAt_pi.2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j = 0`. Substitute `hj` using the available equality. Simplify `h0` using `[chartInv]`.

Simplify `h0.mul (contDiff_apply ℂ ℂ j).contDiffAt` using `[chartInv, hj]`.
-/
theorem contDiffAt_chartInv {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : ContDiffAt ℂ 2 chartInv y := by
  have h0 : ContDiffAt ℂ 2 (fun y : Fin (e + 1) → ℂ => (y 0)⁻¹) y :=
    (contDiff_apply ℂ ℂ (0 : Fin (e + 1))).contDiffAt.inv hy
  refine contDiffAt_pi.2 fun j => ?_
  by_cases hj : j = 0
  · subst hj
    simpa [chartInv] using h0
  · simpa [chartInv, hj] using h0.mul (contDiff_apply ℂ ℂ j).contDiffAt

def logCoord (y : Fin (e + 1) → ℂ) (y' : Fin (e + 1) → ℂ) : ℂ :=
  Complex.log (y' 0 / y 0) + (Real.log ‖y 0‖ : ℂ)

/- English proof (translation)
Rewrite using `[logCoord, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div, Real.log_div (norm_ne_zero_iff.mpr hy') (norm_ne_zero_iff.mpr hy)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem logCoord_re (y y' : Fin (e + 1) → ℂ) (hy : y 0 ≠ 0) (hy' : y' 0 ≠ 0) :
    (logCoord y y').re = Real.log ‖y' 0‖ := by
  rw [logCoord, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr hy') (norm_ne_zero_iff.mpr hy)]
  ring

/- English proof (translation)
Establish `hmem : y 0 / y 0 ∈ Complex.slitPlane`. Rewrite using `[div_self hy]`. Conclude with `Complex.one_mem_slitPlane`. Conclude with `((Complex.contDiffAt_log hmem).comp y ((contDiff_apply ℂ ℂ (0 : Fin (e + 1))).contDiffAt.div_const (y 0))).add contDiffAt_const`.
-/
theorem contDiffAt_logCoord {y : Fin (e + 1) → ℂ} (hy : y 0 ≠ 0) : ContDiffAt ℂ 2 (logCoord y) y := by
  have hmem : y 0 / y 0 ∈ Complex.slitPlane := by
    rw [div_self hy]
    exact Complex.one_mem_slitPlane
  exact ((Complex.contDiffAt_log hmem).comp y
    ((contDiff_apply ℂ ℂ (0 : Fin (e + 1))).contDiffAt.div_const (y 0))).add contDiffAt_const

end ChartEnergySwapHessian

open ChartEnergySwapHessian ChartMongeAmpereAffineInvariance in

/- English proof (translation)
Introduce `e M N hM hN k`. Use `set S := swapFirstTwo e with hS`. Use `set U : Set (Fin (e + 1) → ℂ) := {y | y 0 ≠ 0} with hU`. Establish `hUo : IsOpen U` using `isOpen_ne_fun (continuous_apply 0) continuous_const`. Establish `hUm : MeasurableSet U` using `hUo.measurableSet`.

Establish `hae : ∀ᵐ y ∂(volume : Measure (Fin (e + 1) → ℂ)), y ∈ U` using `by set K : Submodule ℝ (Fin (e + 1) → ℂ) := LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (e + 1) => ℂ) 0) with hK`. Establish `hKtop : K ≠ ⊤` using `fun h => by`. Establish `hm : (Pi.single 0 1 : Fin (e + 1) → ℂ) ∈ K` using `h ▸ Submodule.mem_top`. Simplify using `[hK] at hm`. Establish `h0` using `Measure.addHaar_submodule (volume : Measure (Fin (e + 1) → ℂ)) K hKtop`.

Rewrite using `[ae_iff]`. Use `h0 using 2` and compare the differences between its conclusion and the goal. Use extensionality with `y`. Simplify using `[hK, hU]`. Use `set Φ : Fin (e + 1) → (Fin (e + 1) → ℂ) → ℝ := fun j => if (j : ℕ) < k then hermChartPot M else hermChartPot N with hΦ`.

Use `set f : (Fin (e + 1) → ℂ) → ℝ := fun w => (hermChartPot M w - hermChartPot N w) * maDensity Φ w with hf`. Establish `hpt : ∀ y ∈ U, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) * maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S) else hermChartPot (Sᴴ * N * S)) y = |(fderiv ℝ chartInv y).det| • f (chartInv y)`. Introduce `y hy`. Establish `hy : y 0 ≠ 0` using `hy`. Establish `hev : ∀ᶠ y' in 𝓝 y, y' 0 ≠ 0` using `(continuous_apply 0).continuousAt.eventually_ne hy`.

Establish `hΦ' : ∀ j : Fin (e + 1), (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S) else hermChartPot (Sᴴ * N * S)) j =ᶠ[𝓝 y] fun y' => Φ j (chartInv y') + (logCoord y y').re`. Introduce `j`. Use `filter_upwards [hev] with y' hy'`. Rewrite using `[logCoord_re y y' hy hy']`. Distinguish the cases in `hj : (j : ℕ) < k`.

Simplify using `only [hΦ, hj, if_true]`. Conclude with `hermChartPot_swap M hM y' hy'`. Simplify using `only [hΦ, hj, if_false]`. Conclude with `hermChartPot_swap N hN y' hy'`. Establish `hΦs : ∀ j, ContDiffAt ℝ 2 (Φ j) (chartInv y)` using `fun j => by`.

Distinguish the cases in `hj : (j : ℕ) < k`. Simplify using `only [hΦ, hj, if_true]`. Conclude with `(contDiff_hermChartPot M hM).contDiffAt`. Simplify using `only [hΦ, hj, if_false]`. Conclude with `(contDiff_hermChartPot N hN).contDiffAt`.

Rewrite using `[maDensity_comp_holo _ Φ chartInv (logCoord y) y hΦs (contDiffAt_chartInv hy) (contDiffAt_logCoord hy) hΦ', det_fderiv_real ((contDiffAt_chartInv hy).differentiableAt (by norm_num)), abs_of_nonneg (Complex.normSq_nonneg _), hermChartPot_swap M hM y hy, hermChartPot_swap N hN y hy …`. Expand and normalize the polynomial expressions, which then agree. Establish `hinj : Set.InjOn chartInv U` using `fun a ha b hb hab => by`. Rewrite using `[← chartInv_chartInv (show a 0 ≠ 0 from ha), hab, chartInv_chartInv (show b 0 ≠ 0 from hb)]`. Establish `himage : chartInv '' U = U`.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩ show chartInv x 0 ≠ 0`. Rewrite using `[chartInv_zero]`. Conclude with `inv_ne_zero hx`.

Introduce `hy`. Use `⟨chartInv y, ?_, chartInv_chartInv hy⟩` and prove the remaining obligations. Use `show chartInv y 0 ≠ 0`. Rewrite using `[chartInv_zero]`. Conclude with `inv_ne_zero hy`.

Establish `hderiv : ∀ y ∈ U, HasFDerivWithinAt chartInv (fderiv ℝ chartInv y) U y` using `fun y hy => (((contDiffAt_chartInv (show y 0 ≠ 0 from hy)).restrict_scalars ℝ).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt`. Unfold `chartMixedEnergy`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Measure.restrict_eq_self_of_ae_mem hae]`. Use `_ = ∫ y in U, |(fderiv ℝ chartInv y).det| • f (chartInv y) := setIntegral_congr_fun hUm hpt`.

Use `_ = ∫ y in chartInv '' U, f y := (integral_image_eq_integral_abs_det_fderiv_smul volume hUm hderiv hinj f).symm`. Use `_ = ∫ y in U, f y := by rw [himage]`. Use `_ = ∫ y, f y := by rw [Measure.restrict_eq_self_of_ae_mem hae]`.
-/
theorem ChartEnergySwapInvariant.proof : ChartEnergySwapInvariant.Statement := by
  intro e M N hM hN k
  set S := swapFirstTwo e with hS
  set U : Set (Fin (e + 1) → ℂ) := {y | y 0 ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne_fun (continuous_apply 0) continuous_const
  have hUm : MeasurableSet U := hUo.measurableSet
  have hae : ∀ᵐ y ∂(volume : Measure (Fin (e + 1) → ℂ)), y ∈ U := by
    set K : Submodule ℝ (Fin (e + 1) → ℂ) :=
      LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (e + 1) => ℂ) 0) with hK
    have hKtop : K ≠ ⊤ := fun h => by
      have hm : (Pi.single 0 1 : Fin (e + 1) → ℂ) ∈ K := h ▸ Submodule.mem_top
      simp [hK] at hm
    have h0 := Measure.addHaar_submodule (volume : Measure (Fin (e + 1) → ℂ)) K hKtop
    rw [ae_iff]
    convert h0 using 2
    ext y
    simp [hK, hU]
  set Φ : Fin (e + 1) → (Fin (e + 1) → ℂ) → ℝ :=
    fun j => if (j : ℕ) < k then hermChartPot M else hermChartPot N with hΦ
  set f : (Fin (e + 1) → ℂ) → ℝ := fun w => (hermChartPot M w - hermChartPot N w) * maDensity Φ w with hf
  have hpt : ∀ y ∈ U, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) *
      maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
        else hermChartPot (Sᴴ * N * S)) y = |(fderiv ℝ chartInv y).det| • f (chartInv y) := by
    intro y hy
    have hy : y 0 ≠ 0 := hy
    have hev : ∀ᶠ y' in 𝓝 y, y' 0 ≠ 0 := (continuous_apply 0).continuousAt.eventually_ne hy
    have hΦ' : ∀ j : Fin (e + 1), (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
        else hermChartPot (Sᴴ * N * S)) j =ᶠ[𝓝 y] fun y' => Φ j (chartInv y') + (logCoord y y').re := by
      intro j
      filter_upwards [hev] with y' hy'
      rw [logCoord_re y y' hy hy']
      by_cases hj : (j : ℕ) < k
      · simp only [hΦ, hj, if_true]
        exact hermChartPot_swap M hM y' hy'
      · simp only [hΦ, hj, if_false]
        exact hermChartPot_swap N hN y' hy'
    have hΦs : ∀ j, ContDiffAt ℝ 2 (Φ j) (chartInv y) := fun j => by
      by_cases hj : (j : ℕ) < k
      · simp only [hΦ, hj, if_true]
        exact (contDiff_hermChartPot M hM).contDiffAt
      · simp only [hΦ, hj, if_false]
        exact (contDiff_hermChartPot N hN).contDiffAt
    rw [maDensity_comp_holo _ Φ chartInv (logCoord y) y hΦs (contDiffAt_chartInv hy)
      (contDiffAt_logCoord hy) hΦ', det_fderiv_real ((contDiffAt_chartInv hy).differentiableAt (by norm_num)),
      abs_of_nonneg (Complex.normSq_nonneg _), hermChartPot_swap M hM y hy, hermChartPot_swap N hN y hy, hf,
      smul_eq_mul]
    ring
  have hinj : Set.InjOn chartInv U := fun a ha b hb hab => by
    rw [← chartInv_chartInv (show a 0 ≠ 0 from ha), hab, chartInv_chartInv (show b 0 ≠ 0 from hb)]
  have himage : chartInv '' U = U := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      show chartInv x 0 ≠ 0
      rw [chartInv_zero]
      exact inv_ne_zero hx
    · intro hy
      refine ⟨chartInv y, ?_, chartInv_chartInv hy⟩
      show chartInv y 0 ≠ 0
      rw [chartInv_zero]
      exact inv_ne_zero hy
  have hderiv : ∀ y ∈ U, HasFDerivWithinAt chartInv (fderiv ℝ chartInv y) U y := fun y hy =>
    (((contDiffAt_chartInv (show y 0 ≠ 0 from hy)).restrict_scalars ℝ).differentiableAt
      (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  unfold chartMixedEnergy
  calc ∫ y, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) *
        maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
          else hermChartPot (Sᴴ * N * S)) y
      = ∫ y in U, (hermChartPot (Sᴴ * M * S) y - hermChartPot (Sᴴ * N * S) y) *
        maDensity (fun j : Fin (e + 1) => if (j : ℕ) < k then hermChartPot (Sᴴ * M * S)
          else hermChartPot (Sᴴ * N * S)) y := by
        rw [Measure.restrict_eq_self_of_ae_mem hae]
    _ = ∫ y in U, |(fderiv ℝ chartInv y).det| • f (chartInv y) := setIntegral_congr_fun hUm hpt
    _ = ∫ y in chartInv '' U, f y :=
        (integral_image_eq_integral_abs_det_fderiv_smul volume hUm hderiv hinj f).symm
    _ = ∫ y in U, f y := by rw [himage]
    _ = ∫ y, f y := by rw [Measure.restrict_eq_self_of_ae_mem hae]

end

end GroundTheory.Heights₂.Heights
