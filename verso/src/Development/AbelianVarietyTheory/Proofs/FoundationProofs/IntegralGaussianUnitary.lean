import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalBasisEigenOfInnerMap
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCexpGaussianPlaneStatement
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

/- English proof (translation)
Use `conv_lhs => rw [← e.sum_repr z, ← e.sum_repr w]`. Simplify using `only [map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, he, smul_eq_mul, RingHom.id_apply, mul_ite, mul_one, mul_zero]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[mul_comm]`.
-/
theorem sesq_eq_sum_repr {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (he : ∀ i j, H (e i) (e j) = if i = j then 1 else 0) (z w : V) :
    H z w = ∑ i, e.repr z i * conj (e.repr w i) := by
  conv_lhs => rw [← e.sum_repr z, ← e.sum_repr w]
  simp only [map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, he,
    smul_eq_mul, RingHom.id_apply, mul_ite, mul_one, mul_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

/- English proof (translation)
Use `conv_lhs => rw [← e.sum_repr z]`. Simplify using `only [map_sum, map_smul, hl]`. Simplify using `[Finsupp.single_apply, mul_comm]`.
-/
theorem repr_apply_of_eigen {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (b : V →ₗ[ℂ] V) (l : Fin n → ℂ) (hl : ∀ i, b (e i) = l i • e i) (z : V)
    (i : Fin n) : e.repr (b z) i = l i * e.repr z i := by
  conv_lhs => rw [← e.sum_repr z]
  simp only [map_sum, map_smul, hl]
  simp [Finsupp.single_apply, mul_comm]

/- English proof (translation)
Rewrite using `[← LinearMap.det_toMatrix e, ← Matrix.det_diagonal]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, hl]`. Simplify using `[Matrix.diagonal_apply, Finsupp.single_apply]`.

Apply the tactic sequence `split_ifs with h1 h2 h2 <;> simp_all`.
-/
theorem det_of_eigen {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (e : Module.Basis (Fin n) ℂ V) (b : V →ₗ[ℂ] V) (l : Fin n → ℂ) (hl : ∀ i, b (e i) = l i • e i) :
    LinearMap.det b = ∏ i, l i := by
  rw [← LinearMap.det_toMatrix e, ← Matrix.det_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, hl]
  simp [Matrix.diagonal_apply, Finsupp.single_apply]
  split_ifs with h1 h2 h2 <;> simp_all

/- English proof (translation)
Introduce `V _ _ _ _ _ μ _ H hH a ha hdet`. Take `⟨n, e, l, he, hl⟩` from `GlobalTheory.UnitaryTheta.unitary_exists_orthonormal_eigenbasis V H hH a ha`. Establish `hb : ∀ i, (1 - (a : V →ₗ[ℂ] V)) (e i) = (1 - l i) • e i` using `fun i => by`. Simplify using `[(hl i).2, sub_smul]`. Establish `hd` using `det_of_eigen e _ _ hb`.

Establish `hr : ∀ z i, e.repr (z - a z) i = (1 - l i) * e.repr z i` using `fun z i => by`. Simplify using `using repr_apply_of_eigen e _ _ hb z i`. Establish `hne : ∀ i, 1 - l i ≠ 0` using `fun i => by`. Rewrite `hdet` using `[hd]`. Conclude with `Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)`.

Establish `hre : ∀ i, 0 < (1 - l i).re` using `fun i => by`. Establish `h1 : (l i).re ≤ 1` using `(hl i).1 ▸ re_le_norm (l i)`. Establish `h2 : (l i).re ≠ 1`. Introduce `h`. Apply `hne i` to reduce the goal to its premises.

Establish `h3 : (l i).re * (l i).re + (l i).im * (l i).im = 1`. Rewrite using `[← normSq_apply, normSq_eq_norm_sq, (hl i).1]`. Evaluate the numerical expressions. Establish `h4 : (l i).im = 0`. Rewrite `h3` using `[h]`.

Conclude with `mul_self_eq_zero.1 (by linarith)`. Apply the tactic sequence `apply Complex.ext <;> simp [h, h4]`. Simplify using `only [sub_re, one_re]`. Conclude with `sub_pos.2 (lt_of_le_of_ne h1 h2)`. Set `T : V ≃L[ℂ] (Fin n → ℂ)` to `e.equivFun.toContinuousLinearEquiv`.

Set `Tm : V ≃ᵐ (Fin n → ℂ)` to `T.toHomeomorph.toMeasurableEquiv`. Establish `hT : ∀ z i, Tm z i = e.repr z i` using `fun z i => rfl`. Use `haveI : (μ.map Tm).IsAddHaarMeasure := T.isAddHaarMeasure_map μ`. Establish `hν` using `Measure.isAddLeftInvariant_eq_smul (μ.map Tm) (volume : Measure (Fin n → ℂ))`. Establish `hpos` using `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map Tm) (volume : Measure (Fin n → ℂ))`.

Use `set c := Measure.addHaarScalarFactor (μ.map Tm) (volume : Measure (Fin n → ℂ)) with hc`. Use `⟨(c : ℝ), by exact_mod_cast hpos.ne', fun y v => ?_⟩` and prove the remaining obligations. Set `g : Fin n → ℂ → ℂ` to `fun i z => cexp (-(π : ℂ) * (1 - l i) * (z * conj z) + π * (((1 - l i) * e.repr y i) * conj z) + π * (z * conj (e.repr v i)))`. Establish `hg` using `fun i => GlobalTheory.T.integral_cexp_complex_gaussian_linear (1 - l i) ((1 - l i) * e.repr y i) (e.repr v i) (hre i)`. Establish `hF : (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) = (fun x : Fin n → ℂ => ∏ i, g i (x i)) ∘ Tm`.

Use function extensionality and compare the values at `z`. Simplify using `only [Function.comp, g, hT, ← Complex.exp_sum, sesq_eq_sum_repr H e he, hr, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hint : Integrable (fun x : Fin n → ℂ => ∏ i, g i (x i)) volume` using `Integrable.fintype_prod (f := g) fun i => (hg i).1`. Rewrite using `[hF]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← integrable_map_equiv, hν]`. Conclude with `hint.smul_measure_nnreal`.

Establish `h1` using `integral_map_equiv (μ := μ) Tm (fun x : Fin n → ℂ => ∏ i, g i (x i))`. Simplify using `only [Function.comp_def]`. Rewrite using `[← h1, hν, integral_smul_nnreal_measure, integral_fintype_prod_volume_eq_prod, hd, sesq_eq_sum_repr H e he, Finset.mul_sum, Complex.exp_sum]`. Establish `h2 : ∀ i, ∫ z, g i z = (1 - l i)⁻¹ * cexp (π * (e.repr y i * conj (e.repr v i)))` using `fun i => by`. Rewrite using `[show ∫ z, g i z = _ from (hg i).2]`.

Use `congr 2`. Clear denominators, using `[hne i]` for the nonvanishing conditions. Simplify using `only [h2, Finset.prod_mul_distrib, Finset.prod_inv_distrib, NNReal.smul_def, real_smul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_gaussian_unitary : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∃ κ : ℝ, κ ≠ 0 ∧ ∀ y v : V, Integrable (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) μ ∧ ∫ z, cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * cexp (π * H y v) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet
  obtain ⟨n, e, l, he, hl⟩ := GlobalTheory.UnitaryTheta.unitary_exists_orthonormal_eigenbasis V H hH a ha
  have hb : ∀ i, (1 - (a : V →ₗ[ℂ] V)) (e i) = (1 - l i) • e i := fun i => by
    simp [(hl i).2, sub_smul]
  have hd := det_of_eigen e _ _ hb
  have hr : ∀ z i, e.repr (z - a z) i = (1 - l i) * e.repr z i := fun z i => by
    simpa using repr_apply_of_eigen e _ _ hb z i
  have hne : ∀ i, 1 - l i ≠ 0 := fun i => by
    rw [hd] at hdet
    exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
  have hre : ∀ i, 0 < (1 - l i).re := fun i => by
    have h1 : (l i).re ≤ 1 := (hl i).1 ▸ re_le_norm (l i)
    have h2 : (l i).re ≠ 1 := by
      intro h
      apply hne i
      have h3 : (l i).re * (l i).re + (l i).im * (l i).im = 1 := by
        rw [← normSq_apply, normSq_eq_norm_sq, (hl i).1]; norm_num
      have h4 : (l i).im = 0 := by
        rw [h] at h3
        exact mul_self_eq_zero.1 (by linarith)
      apply Complex.ext <;> simp [h, h4]
    simp only [sub_re, one_re]
    exact sub_pos.2 (lt_of_le_of_ne h1 h2)
  let T : V ≃L[ℂ] (Fin n → ℂ) := e.equivFun.toContinuousLinearEquiv
  let Tm : V ≃ᵐ (Fin n → ℂ) := T.toHomeomorph.toMeasurableEquiv
  have hT : ∀ z i, Tm z i = e.repr z i := fun z i => rfl
  haveI : (μ.map Tm).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hν := Measure.isAddLeftInvariant_eq_smul (μ.map Tm) (volume : Measure (Fin n → ℂ))
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map Tm) (volume : Measure (Fin n → ℂ))
  set c := Measure.addHaarScalarFactor (μ.map Tm) (volume : Measure (Fin n → ℂ)) with hc
  refine ⟨(c : ℝ), by exact_mod_cast hpos.ne', fun y v => ?_⟩
  let g : Fin n → ℂ → ℂ := fun i z => cexp (-(π : ℂ) * (1 - l i) * (z * conj z) +
    π * (((1 - l i) * e.repr y i) * conj z) + π * (z * conj (e.repr v i)))
  have hg := fun i => GlobalTheory.T.integral_cexp_complex_gaussian_linear (1 - l i) ((1 - l i) * e.repr y i) (e.repr v i) (hre i)
  have hF : (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) =
      (fun x : Fin n → ℂ => ∏ i, g i (x i)) ∘ Tm := by
    funext z
    simp only [Function.comp, g, hT, ← Complex.exp_sum, sesq_eq_sum_repr H e he, hr, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hint : Integrable (fun x : Fin n → ℂ => ∏ i, g i (x i)) volume :=
    Integrable.fintype_prod (f := g) fun i => (hg i).1
  rw [hF]
  refine ⟨?_, ?_⟩
  · rw [← integrable_map_equiv, hν]
    exact hint.smul_measure_nnreal
  · have h1 := integral_map_equiv (μ := μ) Tm (fun x : Fin n → ℂ => ∏ i, g i (x i))
    simp only [Function.comp_def]
    rw [← h1, hν, integral_smul_nnreal_measure, integral_fintype_prod_volume_eq_prod, hd,
      sesq_eq_sum_repr H e he, Finset.mul_sum, Complex.exp_sum]
    have h2 : ∀ i, ∫ z, g i z = (1 - l i)⁻¹ * cexp (π * (e.repr y i * conj (e.repr v i))) := fun i => by
      rw [show ∫ z, g i z = _ from (hg i).2]
      congr 2
      field_simp [hne i]
    simp only [h2, Finset.prod_mul_distrib, Finset.prod_inv_distrib, NNReal.smul_def, real_smul]
    ring

end GlobalTheory.UnitaryTheta
