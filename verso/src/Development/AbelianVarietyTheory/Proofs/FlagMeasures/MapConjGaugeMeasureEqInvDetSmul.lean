import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeMeasureMatrixAlgebraSubgroupLocalAsymptoticStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJLieCoordsConjLinearStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJMapConjEqSmulOfNormalizingStatement
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.RightDerivativeZeroOutsideSupport
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.GaugeConjScale

open Topology Filter

/- English proof (translation)
Establish `hc : Continuous (Matrix.toLin' L)` using `LinearMap.continuous_of_finiteDimensional _`. Establish `h` using `Real.map_matrix_volume_pi_eq_smul_volume_pi hL`. Establish `h2 : ∫ t, φ t ∂(Measure.map (Matrix.toLin' L) volume) = ∫ t, φ (Matrix.toLin' L t)` using `integral_map hc.measurable.aemeasurable hφ.aestronglyMeasurable`. Rewrite `h2` using `[h, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul]`. Simplify using `using h2.symm`.
-/
theorem integral_comp_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : Continuous φ) :
    ∫ t, φ (L *ᵥ t) = |L.det|⁻¹ * ∫ t, φ t := by
  have hc : Continuous (Matrix.toLin' L) := LinearMap.continuous_of_finiteDimensional _
  have h := Real.map_matrix_volume_pi_eq_smul_volume_pi hL
  have h2 : ∫ t, φ t ∂(Measure.map (Matrix.toLin' L) volume) = ∫ t, φ (Matrix.toLin' L t) :=
    integral_map hc.measurable.aemeasurable hφ.aestronglyMeasurable
  rw [h, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), abs_inv, smul_eq_mul] at h2
  simpa using h2.symm

/- English proof (translation)
Establish `hu : IsUnit L.det` using `isUnit_iff_ne_zero.2 hL`. Set `e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)` to `(Matrix.toLinearEquiv' L (Matrix.invertibleOfIsUnitDet L hu)).toContinuousLinearEquiv`. Conclude with `hφ.comp_homeomorph e.toHomeomorph`.
-/
theorem hasCompactSupport_comp_mulVec {d : ℕ} (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : HasCompactSupport φ) : HasCompactSupport (fun t => φ (L *ᵥ t)) := by
  have hu : IsUnit L.det := isUnit_iff_ne_zero.2 hL
  let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
    (Matrix.toLinearEquiv' L (Matrix.invertibleOfIsUnitDet L hu)).toContinuousLinearEquiv
  exact hφ.comp_homeomorph e.toHomeomorph

/- English proof (translation)
Establish `hC0 : 0 < C` using `lt_of_lt_of_le one_pos hC`. Set `b : ContDiffBump (0 : Fin d → ℝ)` to `⟨1, 2, one_pos, one_lt_two⟩`. Set `φ : (Fin d → ℝ) → ℝ` to `b`. Establish `hφc : Continuous φ` using `b.continuous`. Establish `hφs : HasCompactSupport φ` using `b.hasCompactSupport`.

Establish `hφp : 0 < ∫ x, φ x` using `b.integral_pos`. Establish `hφ0 : ∀ x, 0 ≤ φ x` using `fun x => b.nonneg`. Establish `hφ1 : ∀ x, φ x ≤ 1` using `fun x => b.le_one`. Set `ψ : (Fin d → ℝ) → ℝ` to `fun x => φ (L *ᵥ x)`. Establish `hψc : Continuous ψ` using `hφc.comp (continuous_const.matrix_mulVec continuous_id)`.

Establish `hψs : HasCompactSupport ψ` using `hasCompactSupport_comp_mulVec L hL φ hφs`. Establish `hψi : ∫ x, ψ x = |L.det|⁻¹ * ∫ x, φ x` using `integral_comp_mulVec L hL φ hφc`. Establish `hr1 : 0 < ρ / C` using `div_pos hρ hC0`. Establish `hr1' : ρ / C ≤ ρ` using `div_le_self hρ.le hC`. Establish `hr2 : 0 < ρ / C / C` using `div_pos hr1 hC0`.

Establish `hr2' : ρ / C / C ≤ ρ` using `(div_le_self hr1.le hC).trans hr1'`. Establish `hB1 : MeasurableSet {g | h g < ρ / C}` using `measurableSet_lt hh measurable_const`. Establish `hs1 : {g | h g < ρ / C / C} ⊆ T ⁻¹' {g | h g < ρ / C}`. Introduce `g hg`. Establish `hg : h g < ρ / C / C` using `hg`.

Rewrite `hg` using `[lt_div_iff₀ hC0]`. Use `h1 g` as an intermediate fact. Use `show h (T g) < ρ / C`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hs2 : T ⁻¹' {g | h g < ρ / C} ⊆ {g | h g < ρ}`.

Introduce `g hg`. Establish `hg : h (T g) < ρ / C` using `hg`. Rewrite `hg` using `[lt_div_iff₀ hC0]`. Use `h2 g` as an intermediate fact. Use `show h g < ρ`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hm : ∀ r : ℝ, Measurable (fun g => (fun i => t g i / r : Fin d → ℝ))` using `fun r => measurable_pi_lambda _ fun i => ((measurable_pi_apply i).comp ht).div_const r`. Establish `hint : ∀ r : ℝ, IntegrableOn (fun g => ψ (fun i => t g i / r)) {g | h g < ρ} μ`. Introduce `r`. Use `Measure.integrableOn_of_bounded (M := 1) hfin (hψc.measurable.comp (hm r)).aestronglyMeasurable ?_` and prove the remaining obligations.

Use `Eventually.of_forall fun g => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]`. Conclude with `hφ1 _`. Establish `key : ∀ r : ℝ, (c : ℝ) * ∫ g in {g | h g < ρ / C}, φ (fun i => t g i / r) ∂μ = ∫ g in T ⁻¹' {g | h g < ρ / C}, ψ (fun i => t g i / r) ∂μ`. Introduce `r`.

Establish `e1` using `setIntegral_map (μ := μ) (g := T) (f := fun g => φ (fun i => t g i / r)) hB1 (hφc.measurable.comp (hm r)).aestronglyMeasurable hT.aemeasurable`. Rewrite `e1` using `[hc, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul]`. Rewrite using `[e1]`. Use `integral_congr_ae (ae_restrict_of_ae (hTt.mono fun g hg => ?_))` and prove the remaining obligations. Establish `e2 : ∀ y : Fin d → ℝ, (fun i => y i / r) = r⁻¹ • y` using `fun y => by`.

Use extensionality with `i`. Simplify using `[div_eq_inv_mul]`. Use `show φ (fun i => t (T g) i / r) = φ (L *ᵥ fun i => t g i / r)`. Rewrite using `[e2, e2, hg, Matrix.mulVec_smul]`. Establish `l1` using `(hlim _ hr1 hr1' φ hφc hφs).const_mul (c : ℝ)`.

Establish `l2` using `hlim _ hr2 hr2' ψ hψc hψs`. Establish `l3` using `hlim _ hρ le_rfl ψ hψc hψs`. Establish `a1 : ∫ x, ψ x ≤ c * ∫ x, φ x`. Use `le_of_tendsto_of_tendsto l2 l1 ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with r hr`.

Establish `hr : 0 < r` using `hr`. Rewrite using `[mul_left_comm, key]`. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations. Conclude with `setIntegral_mono_set ((hint r).mono_set hs2) (Eventually.of_forall fun g => hφ0 _) hs1.eventuallyLE`. Establish `a2 : c * ∫ x, φ x ≤ ∫ x, ψ x`.

Use `le_of_tendsto_of_tendsto l1 l3 ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with r hr`. Establish `hr : 0 < r` using `hr`. Rewrite using `[mul_left_comm, key]`. Use `mul_le_mul_of_nonneg_left ?_ (by positivity)` and prove the remaining obligations.

Conclude with `setIntegral_mono_set (hint r) (Eventually.of_forall fun g => hφ0 _) hs2.eventuallyLE`. Conclude with `mul_right_cancel₀ hφp.ne' ((le_antisymm a2 a1).trans hψi)`.
-/
theorem scalar_eq_inv_det {X : Type} [MeasurableSpace X] (μ : Measure X) (T : X → X) (hT : Measurable T)
    (h : X → ℝ) (hh : Measurable h) {d : ℕ} (t : X → Fin d → ℝ) (ht : Measurable t)
    (L : Matrix (Fin d) (Fin d) ℝ) (hL : L.det ≠ 0) (c : NNReal) (hc : μ.map T = (c : ENNReal) • μ)
    (hTt : ∀ᵐ g ∂μ, t (T g) = L *ᵥ t g) (C : ℝ) (hC : 1 ≤ C) (h1 : ∀ g, h (T g) ≤ C * h g)
    (h2 : ∀ g, h g ≤ C * h (T g)) (ρ : ℝ) (hρ : 0 < ρ) (hfin : μ {g | h g < ρ} ≠ ⊤)
    (hlim : ∀ r₁ : ℝ, 0 < r₁ → r₁ ≤ ρ → ∀ φ : (Fin d → ℝ) → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun r : ℝ => (r ^ d)⁻¹ * ∫ g in {g | h g < r₁}, φ (fun i => t g i / r) ∂μ)
        (𝓝[>] 0) (𝓝 (∫ x, φ x))) :
    (c : ℝ) = |L.det|⁻¹ := by
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  let b : ContDiffBump (0 : Fin d → ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  let φ : (Fin d → ℝ) → ℝ := b
  have hφc : Continuous φ := b.continuous
  have hφs : HasCompactSupport φ := b.hasCompactSupport
  have hφp : 0 < ∫ x, φ x := b.integral_pos
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => b.nonneg
  have hφ1 : ∀ x, φ x ≤ 1 := fun x => b.le_one
  let ψ : (Fin d → ℝ) → ℝ := fun x => φ (L *ᵥ x)
  have hψc : Continuous ψ := hφc.comp (continuous_const.matrix_mulVec continuous_id)
  have hψs : HasCompactSupport ψ := hasCompactSupport_comp_mulVec L hL φ hφs
  have hψi : ∫ x, ψ x = |L.det|⁻¹ * ∫ x, φ x := integral_comp_mulVec L hL φ hφc
  have hr1 : 0 < ρ / C := div_pos hρ hC0
  have hr1' : ρ / C ≤ ρ := div_le_self hρ.le hC
  have hr2 : 0 < ρ / C / C := div_pos hr1 hC0
  have hr2' : ρ / C / C ≤ ρ := (div_le_self hr1.le hC).trans hr1'
  have hB1 : MeasurableSet {g | h g < ρ / C} := measurableSet_lt hh measurable_const
  have hs1 : {g | h g < ρ / C / C} ⊆ T ⁻¹' {g | h g < ρ / C} := by
    intro g hg
    have hg : h g < ρ / C / C := hg
    rw [lt_div_iff₀ hC0] at hg
    have := h1 g
    show h (T g) < ρ / C
    linarith
  have hs2 : T ⁻¹' {g | h g < ρ / C} ⊆ {g | h g < ρ} := by
    intro g hg
    have hg : h (T g) < ρ / C := hg
    rw [lt_div_iff₀ hC0] at hg
    have := h2 g
    show h g < ρ
    linarith
  have hm : ∀ r : ℝ, Measurable (fun g => (fun i => t g i / r : Fin d → ℝ)) := fun r =>
    measurable_pi_lambda _ fun i => ((measurable_pi_apply i).comp ht).div_const r
  have hint : ∀ r : ℝ, IntegrableOn (fun g => ψ (fun i => t g i / r)) {g | h g < ρ} μ := by
    intro r
    refine Measure.integrableOn_of_bounded (M := 1) hfin (hψc.measurable.comp (hm r)).aestronglyMeasurable ?_
    refine Eventually.of_forall fun g => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 _)]
    exact hφ1 _
  have key : ∀ r : ℝ, (c : ℝ) * ∫ g in {g | h g < ρ / C}, φ (fun i => t g i / r) ∂μ
      = ∫ g in T ⁻¹' {g | h g < ρ / C}, ψ (fun i => t g i / r) ∂μ := by
    intro r
    have e1 := setIntegral_map (μ := μ) (g := T) (f := fun g => φ (fun i => t g i / r)) hB1
      (hφc.measurable.comp (hm r)).aestronglyMeasurable hT.aemeasurable
    rw [hc, Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul] at e1
    rw [e1]
    refine integral_congr_ae (ae_restrict_of_ae (hTt.mono fun g hg => ?_))
    have e2 : ∀ y : Fin d → ℝ, (fun i => y i / r) = r⁻¹ • y := fun y => by
      ext i; simp [div_eq_inv_mul]
    show φ (fun i => t (T g) i / r) = φ (L *ᵥ fun i => t g i / r)
    rw [e2, e2, hg, Matrix.mulVec_smul]
  have l1 := (hlim _ hr1 hr1' φ hφc hφs).const_mul (c : ℝ)
  have l2 := hlim _ hr2 hr2' ψ hψc hψs
  have l3 := hlim _ hρ le_rfl ψ hψc hψs
  have a1 : ∫ x, ψ x ≤ c * ∫ x, φ x := by
    refine le_of_tendsto_of_tendsto l2 l1 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    rw [mul_left_comm, key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set ((hint r).mono_set hs2) (Eventually.of_forall fun g => hφ0 _) hs1.eventuallyLE
  have a2 : c * ∫ x, φ x ≤ ∫ x, ψ x := by
    refine le_of_tendsto_of_tendsto l1 l3 ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hr : 0 < r := hr
    rw [mul_left_comm, key]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact setIntegral_mono_set (hint r) (Eventually.of_forall fun g => hφ0 _) hs2.eventuallyLE
  exact mul_right_cancel₀ hφp.ne' ((le_antisymm a2 a1).trans hψi)

/- English proof (translation)
Establish `a : uMat (m * g * m⁻¹) = uMat m * uMat g * uMat m⁻¹` using `rfl`. Establish `b : uMat m * uMat m⁻¹ = 1`. Establish `: uMat m * uMat m⁻¹ = uMat (m * m⁻¹)` using `rfl`. Rewrite using `[this, mul_inv_cancel]`. Both sides reduce to the same expression.

Establish `e : uMat (m * g * m⁻¹) - 1 = uMat m * (uMat g - 1) * uMat m⁻¹`. Rewrite using `[a, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, b]`. Rewrite using `[e]`. Use `(Formalism.REAL.frobenius_mul_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[mul_right_comm]`.

Conclude with `mul_le_mul_of_nonneg_right (Formalism.REAL.frobenius_mul_le _ _) (Formalism.REAL.frobenius_nonneg _)`.
-/
theorem hs_conj_le {n : ℕ} {ε : Fin n → Bool} (m g : Formalism.REAL.UJ ε) :
    Formalism.REAL.hs (uMat (m * g * m⁻¹) - 1) ≤
      Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) * Formalism.REAL.hs (uMat g - 1) := by
  have a : uMat (m * g * m⁻¹) = uMat m * uMat g * uMat m⁻¹ := rfl
  have b : uMat m * uMat m⁻¹ = 1 := by
    have : uMat m * uMat m⁻¹ = uMat (m * m⁻¹) := rfl
    rw [this, mul_inv_cancel]; rfl
  have e : uMat (m * g * m⁻¹) - 1 = uMat m * (uMat g - 1) * uMat m⁻¹ := by
    rw [a, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, b]
  rw [e]
  refine (Formalism.REAL.frobenius_mul_le _ _).trans ?_
  rw [mul_right_comm]
  exact mul_le_mul_of_nonneg_right (Formalism.REAL.frobenius_mul_le _ _) (Formalism.REAL.frobenius_nonneg _)

/- English proof (translation)
Establish `hSe : (S : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A}` using `Set.ext hS`. Take `⟨-, hK, -, r₀, hr₀, hlim⟩` from `GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hE hsp μ (hSe ▸ hμ)`. Take `⟨h1, h2, h3⟩` from `hμ`. Establish `hp : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)` using `Metric.measure_ball_pos _ _ one_pos`. Establish `hf : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) < ⊤` using `measure_ball_lt_top`.

Take `⟨r, ⟨hr1, hr2⟩, hr⟩` from `(((h3.eventually (lt_mem_nhds hp)).and (h3.eventually (gt_mem_nhds hf))).and self_mem_nhdsWithin).exists`. Establish `hr : 0 < r` using `hr`. Establish `hcu : Continuous (fun g : Formalism.REAL.UJ ε => uMat g)` using `Units.continuous_val.comp continuous_subtype_val`. Establish `hc : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1))`. Unfold `Formalism.REAL.hs`.

Use `continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `(((hcu.sub continuous_const).matrix_elem i j).norm).pow 2`. Establish `hne : μ ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hr1`.

Establish `hfin : μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤`. Introduce `h`. Rewrite `hr2` using `[h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]`. Conclude with `lt_irrefl _ hr2`. Take `⟨c, hcμ⟩` from `GlobalTheory.T.unitaryJ_map_conj_eq_smul_of_normalizing n ε S μ hcl h1 h2 hK hne m hm`.

Establish `hC0 : 0 ≤ Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹)` using `mul_nonneg (Formalism.REAL.frobenius_nonneg _) (Formalism.REAL.frobenius_nonneg _)`. Establish `hT : Continuous (fun u : Formalism.REAL.UJ ε => m * u * m⁻¹)` using `by fun_prop`. Establish `ht : Continuous (fun (g : Formalism.REAL.UJ ε) (i : Fin d) => (((uMat g - 1) * (E i)ᴴ).trace).re)` using `continuous_pi fun i => Complex.continuous_re.comp (((hcu.sub continuous_const).matrix_mul continuous_const).matrix_trace)`. Establish `key` using `scalar_eq_inv_det μ (fun u => m * u * m⁻¹) hT.measurable _ hc.measurable _ ht.measurable L hL c hcμ ?_ (Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) + 1) (by linarith) ?_ ?_ (min r₀ (r ^ 2)) (lt_min hr₀ (by positivity)) ?_ (fun r₁ a b => hlim r₁ a (b.trans (min_le_le …`. Rewrite using `[hcμ, ← key, ENNReal.ofReal_coe_nnreal]`.

Establish `: ∀ᵐ g ∂μ, g ∈ (S : Set (Formalism.REAL.UJ ε))` using `h1 filter_upwards [this] with g hg`. Conclude with `GlobalTheory.T.unitaryJ_lieCoords_conj_linear n ε A d E hE hsp g m L ((hS g).1 hg) ((hS _).1 (S.inv_mem hg)) hmL`. Introduce `g`. Use `hs_conj_le m g` as an intermediate fact. Use `Formalism.REAL.frobenius_nonneg (uMat g - 1)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `g`. Establish `h4` using `hs_conj_le m⁻¹ (m * g * m⁻¹)`. Establish `e : m⁻¹ * (m * g * m⁻¹) * m⁻¹⁻¹ = g` using `by group`. Rewrite `h4` using `[e, inv_inv]`.

Use `Formalism.REAL.frobenius_nonneg (uMat (m * g * m⁻¹) - 1)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `ne_top_of_le_ne_top hfin (measure_mono fun g hg => ?_)` and prove the remaining obligations. Establish `hg : Formalism.REAL.hs (uMat g - 1) < min r₀ (r ^ 2)` using `hg`. Conclude with `Real.sqrt_le_iff.2 ⟨hr.le, (hg.trans_le (min_le_right _ _)).le⟩`.
-/
theorem map_conj_eq_inv_det_smul (n : ℕ) (ε : Fin n → Bool) (A : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (S : Subgroup (Formalism.REAL.UJ ε))
    (hA : ∀ X ∈ A, ∀ Y ∈ A, X * Y ∈ A)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ X, (X ∈ A ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E))
    (hS : ∀ g, g ∈ S ↔ uMat g - 1 ∈ A) (hcl : IsClosed (S : Set (Formalism.REAL.UJ ε)))
    (μ : Measure (Formalism.REAL.UJ ε)) (hμ : IsGaugeSub (S : Set (Formalism.REAL.UJ ε)) d μ)
    (m : Formalism.REAL.UJ ε) (L : Matrix (Fin d) (Fin d) ℝ) (hm : ∀ g, g ∈ S ↔ m * g * m⁻¹ ∈ S)
    (hmL : ∀ k, uMat m * E k * uMat m⁻¹ = ∑ i, L i k • E i) (hL : L.det ≠ 0) :
    μ.map (fun u => m * u * m⁻¹) = ENNReal.ofReal |L.det|⁻¹ • μ := by
  have hSe : (S : Set (Formalism.REAL.UJ ε)) = {g | uMat g - 1 ∈ A} := Set.ext hS
  obtain ⟨-, hK, -, r₀, hr₀, hlim⟩ := GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hE hsp μ (hSe ▸ hμ)
  obtain ⟨h1, h2, h3⟩ := hμ
  have hp : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := Metric.measure_ball_pos _ _ one_pos
  have hf : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) < ⊤ := measure_ball_lt_top
  obtain ⟨r, ⟨hr1, hr2⟩, hr⟩ :=
    (((h3.eventually (lt_mem_nhds hp)).and (h3.eventually (gt_mem_nhds hf))).and self_mem_nhdsWithin).exists
  have hr : 0 < r := hr
  have hcu : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
    Units.continuous_val.comp continuous_subtype_val
  have hc : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.REAL.hs (uMat g - 1)) := by
    unfold Formalism.REAL.hs
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((hcu.sub continuous_const).matrix_elem i j).norm).pow 2
  have hne : μ ≠ 0 := by
    rintro rfl
    simp at hr1
  have hfin : μ {g | Real.sqrt (Formalism.REAL.hs (uMat g - 1)) ≤ r} ≠ ⊤ := by
    intro h
    rw [h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top] at hr2
    exact lt_irrefl _ hr2
  obtain ⟨c, hcμ⟩ := GlobalTheory.T.unitaryJ_map_conj_eq_smul_of_normalizing n ε S μ hcl h1 h2 hK hne m hm
  have hC0 : 0 ≤ Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) :=
    mul_nonneg (Formalism.REAL.frobenius_nonneg _) (Formalism.REAL.frobenius_nonneg _)
  have hT : Continuous (fun u : Formalism.REAL.UJ ε => m * u * m⁻¹) := by fun_prop
  have ht : Continuous (fun (g : Formalism.REAL.UJ ε) (i : Fin d) => (((uMat g - 1) * (E i)ᴴ).trace).re) :=
    continuous_pi fun i => Complex.continuous_re.comp
      (((hcu.sub continuous_const).matrix_mul continuous_const).matrix_trace)
  have key := scalar_eq_inv_det μ (fun u => m * u * m⁻¹) hT.measurable _ hc.measurable _ ht.measurable L hL c hcμ
    ?_ (Formalism.REAL.hs (uMat m) * Formalism.REAL.hs (uMat m⁻¹) + 1) (by linarith) ?_ ?_ (min r₀ (r ^ 2))
    (lt_min hr₀ (by positivity)) ?_ (fun r₁ a b => hlim r₁ a (b.trans (min_le_left _ _)))
  · rw [hcμ, ← key, ENNReal.ofReal_coe_nnreal]
  · have : ∀ᵐ g ∂μ, g ∈ (S : Set (Formalism.REAL.UJ ε)) := h1
    filter_upwards [this] with g hg
    exact GlobalTheory.T.unitaryJ_lieCoords_conj_linear n ε A d E hE hsp g m L ((hS g).1 hg) ((hS _).1 (S.inv_mem hg)) hmL
  · intro g
    have := hs_conj_le m g
    have := Formalism.REAL.frobenius_nonneg (uMat g - 1)
    linarith
  · intro g
    have h4 := hs_conj_le m⁻¹ (m * g * m⁻¹)
    have e : m⁻¹ * (m * g * m⁻¹) * m⁻¹⁻¹ = g := by group
    rw [e, inv_inv] at h4
    have := Formalism.REAL.frobenius_nonneg (uMat (m * g * m⁻¹) - 1)
    linarith
  · refine ne_top_of_le_ne_top hfin (measure_mono fun g hg => ?_)
    have hg : Formalism.REAL.hs (uMat g - 1) < min r₀ (r ^ 2) := hg
    exact Real.sqrt_le_iff.2 ⟨hr.le, (hg.trans_le (min_le_right _ _)).le⟩

end GlobalTheory.GaugeConjScale
