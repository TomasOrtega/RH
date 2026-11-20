import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
  [CompleteSpace E] [CompleteSpace F]

/- English proof (translation)
Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_add_right, inner_smul_right, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]`. Simplify using `[← Complex.ofReal_pow]`.
-/
theorem kerProj_re_inner_reg (T : E →L[ℂ] F) (t : ℝ) (w : E) :
    (⟪w, (ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E)) w⟫_ℂ).re
      = ‖T w‖ ^ 2 + t * ‖w‖ ^ 2 := by
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, inner_add_right,
    inner_smul_right, ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp [← Complex.ofReal_pow]

/- English proof (translation)
Rewrite using `[ContinuousLinearMap.isUnit_iff_bijective]`. Use `set B := ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E) with hB`. Establish `hinj : Function.Injective B`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `w hw`.

Establish `h` using `kerProj_re_inner_reg T t w`. Rewrite `h` using `[← hB, hw]`. Simplify using `only [inner_zero_right, Complex.zero_re] at h`. Establish `h1 : t * ‖w‖ ^ 2 ≤ 0` using `by nlinarith [sq_nonneg ‖T w‖]`. Establish `h2 : ‖w‖ ^ 2 ≤ 0`.

Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Use polynomial arithmetic with `[mul_pos ht hc]`. Establish `: ‖w‖ = 0` using `by nlinarith [norm_nonneg w]`. Conclude with `norm_eq_zero.mp this`.

Conclude with `⟨hinj, (LinearMap.injective_iff_surjective (f := (B : E →ₗ[ℂ] E))).mp hinj⟩`.
-/
theorem kerProj_isUnit_reg (T : E →L[ℂ] F) {t : ℝ} (ht : 0 < t) :
    IsUnit (ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E)) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  set B := ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E) with hB
  have hinj : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have h := kerProj_re_inner_reg T t w
    rw [← hB, hw] at h
    simp only [inner_zero_right, Complex.zero_re] at h
    have h1 : t * ‖w‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖T w‖]
    have h2 : ‖w‖ ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      nlinarith [mul_pos ht hc]
    have : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
    exact norm_eq_zero.mp this
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (B : E →ₗ[ℂ] E))).mp hinj⟩

/- English proof (translation)
Establish `hu` using `kerProj_isUnit_reg T ht`. Use `set B := ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E) with hB`. Use `set w := (t : ℂ) • Ring.inverse B (k + ContinuousLinearMap.adjoint T z) - k with hw`. Establish `hBk : B k = (t : ℂ) • k` using `by simp [hB, hk]`. Establish `hBw : B w = (t : ℂ) • ContinuousLinearMap.adjoint T z`.

Establish `: B (Ring.inverse B (k + ContinuousLinearMap.adjoint T z)) = k + ContinuousLinearMap.adjoint T z`. Rewrite using `[← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu]`. Both sides reduce to the same expression. Rewrite using `[hw, map_sub, map_smul, this, hBk, smul_add]`. Normalize the expressions using the abelian group laws.

Establish `h` using `kerProj_re_inner_reg T t w`. Rewrite `h` using `[← hB, hBw, inner_smul_right, ContinuousLinearMap.adjoint_inner_right, Complex.re_ofReal_mul]`. Establish `h1 : (⟪T w, z⟫_ℂ).re ≤ ‖T w‖ * ‖z‖` using `(Complex.re_le_norm _).trans (norm_inner_le_norm _ _)`. Establish `h2 : ‖T w‖ ^ 2 + t * ‖w‖ ^ 2 ≤ t * (‖T w‖ * ‖z‖)`. Rewrite using `[← h]`.

Conclude with `mul_le_mul_of_nonneg_left h1 ht.le`. Establish `h3 : t * ‖w‖ ^ 2 ≤ t * (t * ‖z‖ ^ 2)`. Use polynomial arithmetic with `[sq_nonneg (‖T w‖ - t * ‖z‖), sq_nonneg ‖T w‖, sq_nonneg (t * ‖z‖)]`. Conclude with `le_of_mul_le_mul_left h3 ht`.
-/
theorem kerProj_reg_estimate (T : E →L[ℂ] F) {t : ℝ} (ht : 0 < t) (k : E) (z : F)
    (hk : T k = 0) :
    ‖(t : ℂ) • Ring.inverse (ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E))
      (k + ContinuousLinearMap.adjoint T z) - k‖ ^ 2 ≤ t * ‖z‖ ^ 2 := by
  have hu := kerProj_isUnit_reg T ht
  set B := ContinuousLinearMap.adjoint T ∘L T + (t : ℂ) • (1 : E →L[ℂ] E) with hB
  set w := (t : ℂ) • Ring.inverse B (k + ContinuousLinearMap.adjoint T z) - k with hw
  have hBk : B k = (t : ℂ) • k := by simp [hB, hk]
  have hBw : B w = (t : ℂ) • ContinuousLinearMap.adjoint T z := by
    have : B (Ring.inverse B (k + ContinuousLinearMap.adjoint T z))
        = k + ContinuousLinearMap.adjoint T z := by
      rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ hu]; rfl
    rw [hw, map_sub, map_smul, this, hBk, smul_add]; abel
  have h := kerProj_re_inner_reg T t w
  rw [← hB, hBw, inner_smul_right, ContinuousLinearMap.adjoint_inner_right,
    Complex.re_ofReal_mul] at h
  have h1 : (⟪T w, z⟫_ℂ).re ≤ ‖T w‖ * ‖z‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have h2 : ‖T w‖ ^ 2 + t * ‖w‖ ^ 2 ≤ t * (‖T w‖ * ‖z‖) := by
    rw [← h]; exact mul_le_mul_of_nonneg_left h1 ht.le
  have h3 : t * ‖w‖ ^ 2 ≤ t * (t * ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg (‖T w‖ - t * ‖z‖), sq_nonneg ‖T w‖, sq_nonneg (t * ‖z‖)]
  exact le_of_mul_le_mul_left h3 ht

/- English proof (translation)
Use `set K := LinearMap.ker (T : E →ₗ[ℂ] F) with hK`. Establish `hmem : v - K.starProjection v ∈ Kᗮ` using `K.sub_starProjection_mem_orthogonal v`. Establish `horth : Kᗮ = LinearMap.range (LinearMap.adjoint (T : E →ₗ[ℂ] F))` using `LinearMap.orthogonal_ker _`. Rewrite `hmem` using `[horth]`. Take `⟨z, hz⟩` from `hmem`.

Establish `hz' : ContinuousLinearMap.adjoint T z = v - K.starProjection v`. Rewrite using `[← hz]`. Both sides reduce to the same expression. Establish `hk : T (K.starProjection v) = 0` using `K.starProjection_apply_mem v`. Establish `hv : v = K.starProjection v + ContinuousLinearMap.adjoint T z` using `by rw [hz']; abel`.

Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `hlim : Filter.Tendsto (fun j : ℕ => Real.sqrt ((1 / ((j : ℝ) + 1)) * ‖z‖ ^ 2)) Filter.atTop (nhds 0)`. Use `((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (‖z‖ ^ 2)).sqrt` as an intermediate fact. Simplify using `using this`. Use `squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hlim` and prove the remaining obligations.

Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Use `kerProj_reg_estimate T (t := 1 / ((j : ℝ) + 1)) (by positivity) _ z hk` as an intermediate fact. Rewrite `this` using `[← hv]`. Then use the resulting hypothesis.
-/
theorem kerProj_reg_tendsto (T : E →L[ℂ] F) (v : E) :
    Filter.Tendsto (fun j : ℕ => (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) •
      Ring.inverse (ContinuousLinearMap.adjoint T ∘L T
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) v) Filter.atTop
      (nhds ((LinearMap.ker (T : E →ₗ[ℂ] F)).starProjection v)) := by
  set K := LinearMap.ker (T : E →ₗ[ℂ] F) with hK
  have hmem : v - K.starProjection v ∈ Kᗮ := K.sub_starProjection_mem_orthogonal v
  have horth : Kᗮ = LinearMap.range (LinearMap.adjoint (T : E →ₗ[ℂ] F)) :=
    LinearMap.orthogonal_ker _
  rw [horth] at hmem
  obtain ⟨z, hz⟩ := hmem
  have hz' : ContinuousLinearMap.adjoint T z = v - K.starProjection v := by
    rw [← hz]; rfl
  have hk : T (K.starProjection v) = 0 := K.starProjection_apply_mem v
  have hv : v = K.starProjection v + ContinuousLinearMap.adjoint T z := by rw [hz']; abel
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Filter.Tendsto (fun j : ℕ => Real.sqrt ((1 / ((j : ℝ) + 1)) * ‖z‖ ^ 2))
      Filter.atTop (nhds 0) := by
    have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const (‖z‖ ^ 2)).sqrt
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hlim
  apply Real.le_sqrt_of_sq_le
  have := kerProj_reg_estimate T (t := 1 / ((j : ℝ) + 1)) (by positivity) _ z hk
  rwa [← hv] at this

/- English proof (translation)
Use `measurable_of_tendsto_metrizable (f := fun (j : ℕ) x => (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • Ring.inverse (ContinuousLinearMap.adjoint (T x) ∘L (T x) + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) (v x)) (fun j => ?_) ?_` and prove the remaining obligations. Apply `Continuous.measurable` to reduce the goal to its premises. Apply `Continuous.const_smul` to reduce the goal to its premises. Use `Continuous.clm_apply ?_ hv` and prove the remaining obligations. Establish `hc : Continuous fun x => ContinuousLinearMap.adjoint (T x) ∘L (T x) + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)` using `((ContinuousLinearMap.adjoint.continuous.comp hT).clm_comp hT).add continuous_const`.

Rewrite using `[continuous_iff_continuousAt]`. Introduce `x`. Take `⟨u, hu⟩` from `kerProj_isUnit_reg (T x) (t := 1 / ((j : ℝ) + 1)) (by positivity)`. Establish `h1` using `NormedRing.inverse_continuousAt u`. Rewrite `h1` using `[hu]`.

Conclude with `ContinuousAt.comp (f := fun x => ContinuousLinearMap.adjoint (T x) ∘L (T x) + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) h1 hc.continuousAt`. Rewrite using `[tendsto_pi_nhds]`. Introduce `x`. Conclude with `kerProj_reg_tendsto (T x) (v x)`.
-/
theorem measurable_starProjection_ker_clm {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [MeasurableSpace E] [BorelSpace E] (T : X → E →L[ℂ] F) (v : X → E)
    (hT : Continuous T) (hv : Continuous v) :
    Measurable fun x => (LinearMap.ker (T x : E →ₗ[ℂ] F)).starProjection (v x) := by
  refine measurable_of_tendsto_metrizable (f := fun (j : ℕ) x => (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) •
      Ring.inverse (ContinuousLinearMap.adjoint (T x) ∘L (T x)
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) (v x)) (fun j => ?_) ?_
  · apply Continuous.measurable
    apply Continuous.const_smul
    refine Continuous.clm_apply ?_ hv
    have hc : Continuous fun x => ContinuousLinearMap.adjoint (T x) ∘L (T x)
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E) :=
      ((ContinuousLinearMap.adjoint.continuous.comp hT).clm_comp hT).add continuous_const
    rw [continuous_iff_continuousAt]
    intro x
    obtain ⟨u, hu⟩ := kerProj_isUnit_reg (T x) (t := 1 / ((j : ℝ) + 1)) (by positivity)
    have h1 := NormedRing.inverse_continuousAt u
    rw [hu] at h1
    exact ContinuousAt.comp (f := fun x => ContinuousLinearMap.adjoint (T x) ∘L (T x)
        + (((1 / ((j : ℝ) + 1) : ℝ)) : ℂ) • (1 : E →L[ℂ] E)) h1 hc.continuousAt
  · rw [tendsto_pi_nhds]
    intro x
    exact kerProj_reg_tendsto (T x) (v x)

end

/- English proof (translation)
Introduce `X _ _ _ n p L v hL hv`. Set `Φ : Matrix (Fin p) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin p))` to `(LinearMap.toContinuousLinearMap.toLinearMap).comp Matrix.toEuclideanLin.toLinearMap`. Establish `hΦ : Continuous Φ` using `Φ.continuous_of_finiteDimensional`. Conclude with `measurable_starProjection_ker_clm (fun x => Φ (L x)) v (hΦ.comp hL) hv`.
-/
theorem measurable_starProjection_ker_matrix : ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (n p : ℕ) (L : X → Matrix (Fin p) (Fin n) ℂ) (v : X → EuclideanSpace ℂ (Fin n)), Continuous L → Continuous v → Measurable fun x => (LinearMap.ker (Matrix.toEuclideanLin (L x))).starProjection (v x) := by
  intro X _ _ _ n p L v hL hv
  let Φ : Matrix (Fin p) (Fin n) ℂ →ₗ[ℂ] (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin p)) :=
    (LinearMap.toContinuousLinearMap.toLinearMap).comp Matrix.toEuclideanLin.toLinearMap
  have hΦ : Continuous Φ := Φ.continuous_of_finiteDimensional
  exact measurable_starProjection_ker_clm (fun x => Φ (L x)) v (hΦ.comp hL) hv

end GlobalTheory
