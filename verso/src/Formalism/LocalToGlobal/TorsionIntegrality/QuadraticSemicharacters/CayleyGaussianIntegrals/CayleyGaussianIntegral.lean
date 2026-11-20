import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyIdentity

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Formalism.L2.Th1.H

/- English proof (translation)
Establish `hl0 : l ≠ 0` using `fun h => by simp [h] at hl`. Establish `hπ : (Real.pi : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.mpr Real.pi_ne_zero`. Establish `hb : 0 < ((Real.pi : ℂ) * l).re`. Simplify using `only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]`. Conclude with `mul_pos Real.pi_pos hl`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 (0 : ℂ)` as an intermediate fact. Simplify using `using this`. Rewrite using `[GaussianFourier.integral_cexp_neg_mul_sq_norm (V := ℂ) hb, Complex.finrank_real_complex]`. Rewrite using `[show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num, Complex.cpow_one]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem gauss_plane (l : ℂ) (hl : 0 < l.re) :
    Integrable (fun z : ℂ => Complex.exp (-((Real.pi : ℂ) * l) * ((‖z‖ : ℝ) : ℂ) ^ 2)) ∧
      ∫ z : ℂ, Complex.exp (-((Real.pi : ℂ) * l) * ((‖z‖ : ℝ) : ℂ) ^ 2) = l⁻¹ := by
  have hl0 : l ≠ 0 := fun h => by simp [h] at hl
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hb : 0 < ((Real.pi : ℂ) * l).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_pos Real.pi_pos hl
  refine ⟨?_, ?_⟩
  · have := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb 0 (0 : ℂ)
    simpa using this
  · rw [GaussianFourier.integral_cexp_neg_mul_sq_norm (V := ℂ) hb, Complex.finrank_real_complex]
    rw [show ((2 : ℕ) : ℂ) / 2 = 1 by norm_num, Complex.cpow_one]
    field_simp

/- English proof (translation)
Establish `hfun : (fun w : n → ℂ => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2)) = fun w => ∏ i, Complex.exp (-((Real.pi : ℂ) * l i) * ((‖w i‖ : ℝ) : ℂ) ^ 2)`. Use function extensionality and compare the values at `w`. Rewrite using `[← Complex.exp_sum, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `Integrable.fintype_prod (f := fun i (z : ℂ) => Complex.exp (-((Real.pi : ℂ) * l i) * ((‖z‖ : ℝ) : ℂ) ^ 2)) (fun i => (gauss_plane (l i) (hl i)).1)`. Rewrite using `[integral_fintype_prod_volume_eq_prod (fun i (z : ℂ) => Complex.exp (-((Real.pi : ℂ) * l i) * ((‖z‖ : ℝ) : ℂ) ^ 2)), ← Finset.prod_inv_distrib]`.

Conclude with `Finset.prod_congr rfl fun i _ => (gauss_plane (l i) (hl i)).2`.
-/
theorem gauss_pi {n : Type*} [Fintype n] (l : n → ℂ) (hl : ∀ i, 0 < (l i).re) :
    Integrable (fun w : n → ℂ => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2)) ∧
      ∫ w : n → ℂ, Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2) = (∏ i, l i)⁻¹ := by
  have hfun : (fun w : n → ℂ => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2)) =
      fun w => ∏ i, Complex.exp (-((Real.pi : ℂ) * l i) * ((‖w i‖ : ℝ) : ℂ) ^ 2) := by
    funext w
    rw [← Complex.exp_sum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hfun]
  refine ⟨?_, ?_⟩
  · exact Integrable.fintype_prod
      (f := fun i (z : ℂ) => Complex.exp (-((Real.pi : ℂ) * l i) * ((‖z‖ : ℝ) : ℂ) ^ 2))
      (fun i => (gauss_plane (l i) (hl i)).1)
  · rw [integral_fintype_prod_volume_eq_prod
      (fun i (z : ℂ) => Complex.exp (-((Real.pi : ℂ) * l i) * ((‖z‖ : ℝ) : ℂ) ^ 2)),
      ← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => (gauss_plane (l i) (hl i)).2

/- English proof (translation)
Set `Ψ : (n → ℂ) ≃L[ℂ] V` to `Φ.toContinuousLinearEquiv`. Set `ν : Measure V` to `Measure.map Ψ volume`. Establish `hme : MeasurableEmbedding Ψ` using `Ψ.toHomeomorph.measurableEmbedding`. Take `⟨c, hμ⟩ : ∃ c : NNReal, μ = c • ν` from `⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩`. Substitute `hμ` using the available equality.

Use `⟨(c : ℝ), fun f => ⟨fun hf => ?_, ?_⟩⟩` and prove the remaining obligations. Apply `Integrable.smul_measure_nnreal` to reduce the goal to its premises. Rewrite using `[hme.integrable_map_iff]`. Conclude with `hf`. Apply the tactic sequence `rw [integral_smul_nnreal_measure, hme.integral_map, NNReal.smul_def, Complex.real_smul] try rfl`.
-/
theorem haar_transfer {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {n : Type*} [Fintype n] (Φ : (n → ℂ) ≃ₗ[ℂ] V) :
    ∃ κ : ℝ, ∀ f : V → ℂ, (Integrable (fun w => f (Φ w)) → Integrable f μ) ∧
      ∫ z, f z ∂μ = (κ : ℂ) * ∫ w, f (Φ w) := by
  classical
  let Ψ : (n → ℂ) ≃L[ℂ] V := Φ.toContinuousLinearEquiv
  let ν : Measure V := Measure.map Ψ volume
  have hme : MeasurableEmbedding Ψ := Ψ.toHomeomorph.measurableEmbedding
  obtain ⟨c, hμ⟩ : ∃ c : NNReal, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  subst hμ
  refine ⟨(c : ℝ), fun f => ⟨fun hf => ?_, ?_⟩⟩
  · apply Integrable.smul_measure_nnreal
    rw [hme.integrable_map_iff]
    exact hf
  · rw [integral_smul_nnreal_measure, hme.integral_map, NNReal.smul_def, Complex.real_smul]
    try rfl

/- English proof (translation)
Introduce `V _ _ _ _ _ μ _ H hH hP δ Ae hδ hAe`. Take `⟨b, l, hb, hbl, hl⟩` from `unitary_diag H hH hP δ Ae hδ hAe`. Take `⟨κ, hκ⟩` from `haar_transfer μ b.equivFun.symm`. Establish `hq : (fun w => gq H Ae (b.equivFun.symm w)) = fun w => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2)`. Use function extensionality and compare the values at `w`.

Establish `h1` using `form_of_diag H b l (Ae : V →ₗ[ℂ] V) hb hbl w`. Simplify using `only [LinearEquiv.coe_coe] at h1`. Unfold `gq`. Rewrite using `[h1]`. Establish `hw : (fun w => ((wt H (b.equivFun.symm w) : ℝ) : ℂ)) = fun w => Complex.exp (-(Real.pi : ℂ) * ∑ i, (fun _ => (1 : ℂ)) i * ((‖w i‖ : ℝ) : ℂ) ^ 2)`.

Use function extensionality and compare the values at `w`. Establish `h1` using `form_of_diag H b (fun _ => (1 : ℂ)) LinearMap.id hb (fun i => by simp) w`. Simplify using `only [LinearMap.id_apply] at h1`. Establish `hs : (∑ i, (fun _ => (1 : ℂ)) i * ((‖w i‖ : ℝ) : ℂ) ^ 2) = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ)`. Use `push_cast`.

Simplify using the standard rewrite rules. Unfold `wt`. Rewrite using `[h1, hs, Complex.ofReal_re, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]`. Establish `hgq` using `gauss_pi l hl`. Establish `hgw` using `gauss_pi (n := Fin (Module.finrank ℂ V)) (fun _ => (1 : ℂ)) (fun _ => by simp)`.

Rewrite `hgq` using `[← hq]`. Rewrite `hgw` using `[← hw]`. Use `⟨(hκ _).1 hgq.1, ?_⟩` and prove the remaining obligations. Rewrite using `[(hκ (gq H Ae)).2, hgq.2, ← integral_complex_ofReal, (hκ (fun z => ((wt H z : ℝ) : ℂ))).2, hgw.2, det_of_diag b l (Ae : V →ₗ[ℂ] V) hbl]`. Simplify using `[div_eq_mul_inv]`.
-/
theorem cayleyGaussianIntegral : GaussQuad := by
  intro V _ _ _ _ _ μ _ H hH hP δ Ae hδ hAe
  classical
  obtain ⟨b, l, hb, hbl, hl⟩ := unitary_diag H hH hP δ Ae hδ hAe
  obtain ⟨κ, hκ⟩ := haar_transfer μ b.equivFun.symm
  have hq : (fun w => gq H Ae (b.equivFun.symm w)) =
      fun w => Complex.exp (-(Real.pi : ℂ) * ∑ i, l i * ((‖w i‖ : ℝ) : ℂ) ^ 2) := by
    funext w
    have h1 := form_of_diag H b l (Ae : V →ₗ[ℂ] V) hb hbl w
    simp only [LinearEquiv.coe_coe] at h1
    unfold gq
    rw [h1]
  have hw : (fun w => ((wt H (b.equivFun.symm w) : ℝ) : ℂ)) =
      fun w => Complex.exp (-(Real.pi : ℂ) * ∑ i, (fun _ => (1 : ℂ)) i * ((‖w i‖ : ℝ) : ℂ) ^ 2) := by
    funext w
    have h1 := form_of_diag H b (fun _ => (1 : ℂ)) LinearMap.id hb (fun i => by simp) w
    simp only [LinearMap.id_apply] at h1
    have hs : (∑ i, (fun _ => (1 : ℂ)) i * ((‖w i‖ : ℝ) : ℂ) ^ 2) = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      simp
    unfold wt
    rw [h1, hs, Complex.ofReal_re, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  have hgq := gauss_pi l hl
  have hgw := gauss_pi (n := Fin (Module.finrank ℂ V)) (fun _ => (1 : ℂ)) (fun _ => by simp)
  rw [← hq] at hgq
  rw [← hw] at hgw
  refine ⟨(hκ _).1 hgq.1, ?_⟩
  rw [(hκ (gq H Ae)).2, hgq.2, ← integral_complex_ofReal, (hκ (fun z => ((wt H z : ℝ) : ℂ))).2, hgw.2,
    det_of_diag b l (Ae : V →ₗ[ℂ] V) hbl]
  simp [div_eq_mul_inv]

end Formalism.L2.Th1.H
