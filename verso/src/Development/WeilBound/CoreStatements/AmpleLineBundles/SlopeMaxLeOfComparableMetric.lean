import Development.WeilBound.CoreStatements.AmpleLineBundles.NormDegreeLeOfMetricBoundedMap
import Development.WeilBound.CoreStatements.AmpleLineBundles.StandardHermitianBundleSemistable

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
Establish `h` using `HermitianMetric.standard_inner K (Fin r) σ y y`. Unfold `sqAt`. Use `erw [h]`. Simplify using `only [Complex.conj_mul', Complex.re_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Complex.ofReal_pow, Complex.ofReal_re]`.
-/
theorem sqAt_std (r : ℕ) (σ : K →+* ℂ) (y : Fibre σ (Fin r → 𝓞 K)) :
    sqAt (HermitianBundle.standard K r) σ y = ∑ a, ‖standardCoord K σ (Fin r) y a‖ ^ 2 := by
  have h := HermitianMetric.standard_inner K (Fin r) σ y y
  unfold sqAt
  erw [h]
  simp only [Complex.conj_mul', Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

omit [NumberField K] in
/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul z f`. Establish `hc : ∀ a, ComplexAt.ofComplex σ (standardCoord K σ (Fin r) (z ⊗ₜ f) a) = f a • z`. Introduce `a`.

Simplify using `[standardCoord]`. Simplify using `only [hc, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply, TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul']`. Consider the case `add x y hx hy`. Simplify using `only [map_add, WithLp.ofLp_add, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]`.
-/
theorem sum_coord {M : Type} [AddCommGroup M] [Module (𝓞 K) M] {r : ℕ}
    (b : Module.Basis (Fin r) (𝓞 K) M) (σ : K →+* ℂ) (y : Fibre σ (Fin r → 𝓞 K)) :
    ∑ a, ComplexAt.ofComplex σ (standardCoord K σ (Fin r) y a) ⊗ₜ[𝓞 K] b a =
      b.equivFun.symm.toLinearMap.lTensor (ComplexAt σ) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul z f =>
    have hc : ∀ a, ComplexAt.ofComplex σ (standardCoord K σ (Fin r) (z ⊗ₜ f) a) = f a • z := by
      intro a
      simp [standardCoord]
    simp only [hc, LinearMap.lTensor_tmul, LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply,
      TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    simp only [map_add, WithLp.ofLp_add, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]

/- English proof (translation)
Introduce `K _ _ E r b C hC h`. Establish `hC0 : 0 < C` using `by linarith`. Set `φ : E.carrier →ₗ[𝓞 K] (HermitianBundle.standard K r).carrier` to `b.equivFun.toLinearMap`. Set `ψ : (HermitianBundle.standard K r).carrier →ₗ[𝓞 K] E.carrier` to `b.equivFun.symm.toLinearMap`. Establish `hb : ∀ (σ : K →+* ℂ) (y : Fibre σ (HermitianBundle.standard K r).carrier), C⁻¹ * sqAt (HermitianBundle.standard K r) σ y ≤ sqAt E σ (ψ.lTensor (ComplexAt σ) y) ∧ sqAt E σ (ψ.lTensor (ComplexAt σ) y) ≤ C * sqAt (HermitianBundle.standard K r) σ y`.

Introduce `σ y`. Use `h σ fun a => standardCoord K σ (Fin r) y a` as an intermediate fact. Rewrite `this` using `[sum_coord b σ y, ← sqAt_std r σ y]`. Conclude with `this`. Establish `hψφ : ψ ∘ₗ φ = LinearMap.id` using `LinearMap.ext fun x => b.equivFun.symm_apply_apply x`.

Establish `h1` using `normDegree_le_of_metric_bounded_map K E (HermitianBundle.standard K r) φ C b.equivFun.injective hC0 (fun σ x => by`. Use `(hb σ (φ.lTensor (ComplexAt σ) x)).1` as an intermediate fact. Rewrite `this` using `[← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hψφ, LinearMap.lTensor_id, LinearMap.id_apply, inv_mul_le_iff₀ hC0]`. Conclude with `this)`. Establish `h2` using `normDegree_le_of_metric_bounded_map K (HermitianBundle.standard K r) E ψ C b.equivFun.symm.injective hC0 fun σ y => (hb σ y).2`.

Take `⟨s1, s2⟩` from `standard_hermitian_bundle_semistable K r`. Use `⟨h1.2.trans ?_, ?_⟩` and prove the remaining obligations. Use `(add_le_add_left s1 _).trans ?_` and prove the remaining obligations. Rewrite using `[zero_add]`. Establish `a` using `h1.1 ⊤`.

Establish `c` using `h2.1 ⊤`. Establish `e1 : (⊤ : Submodule (𝓞 K) E.carrier).map φ = ⊤`. Rewrite using `[Submodule.map_top]`. Conclude with `LinearMap.range_eq_top.mpr b.equivFun.surjective`. Establish `e2 : (⊤ : Submodule (𝓞 K) (HermitianBundle.standard K r).carrier).map ψ = ⊤`.

Rewrite using `[Submodule.map_top]`. Conclude with `LinearMap.range_eq_top.mpr b.equivFun.symm.surjective`. Establish `r1 : E.rank ⊤ = r`. Rewrite using `[HermitianBundle.rank, finrank_top, Module.finrank_eq_card_basis b, Fintype.card_fin]`. Establish `r2 : (HermitianBundle.standard K r).rank ⊤ = r`.

Rewrite using `[HermitianBundle.rank, finrank_top]`. Conclude with `Module.finrank_fin_fun (𝓞 K)`. Rewrite `a` using `[e1, s2, r1]`. Rewrite `c` using `[e2, s2, r2]`. Rewrite using `[abs_le]`.

Apply the tactic sequence `constructor <;> linarith`.
-/
theorem slopeMax_le_of_comparable_metric : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (r : ℕ) (b : Module.Basis (Fin r) (𝓞 K) E.carrier) (C : ℝ), 1 ≤ C → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) ≤ C * ∑ a, ‖w a‖ ^ 2) → E.slopeMax ≤ ((Real.log C / 2 : ℝ) : EReal) ∧ |E.normDegree ⊤| ≤ r / 2 * Real.log C := by
  intro K _ _ E r b C hC h
  have hC0 : 0 < C := by linarith
  let φ : E.carrier →ₗ[𝓞 K] (HermitianBundle.standard K r).carrier := b.equivFun.toLinearMap
  let ψ : (HermitianBundle.standard K r).carrier →ₗ[𝓞 K] E.carrier := b.equivFun.symm.toLinearMap
  have hb : ∀ (σ : K →+* ℂ) (y : Fibre σ (HermitianBundle.standard K r).carrier),
      C⁻¹ * sqAt (HermitianBundle.standard K r) σ y ≤ sqAt E σ (ψ.lTensor (ComplexAt σ) y) ∧
      sqAt E σ (ψ.lTensor (ComplexAt σ) y) ≤ C * sqAt (HermitianBundle.standard K r) σ y := by
    intro σ y
    have := h σ fun a => standardCoord K σ (Fin r) y a
    rw [sum_coord b σ y, ← sqAt_std r σ y] at this
    exact this
  have hψφ : ψ ∘ₗ φ = LinearMap.id := LinearMap.ext fun x => b.equivFun.symm_apply_apply x
  have h1 := normDegree_le_of_metric_bounded_map K E (HermitianBundle.standard K r) φ C b.equivFun.injective hC0 (fun σ x => by
    have := (hb σ (φ.lTensor (ComplexAt σ) x)).1
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hψφ, LinearMap.lTensor_id,
      LinearMap.id_apply, inv_mul_le_iff₀ hC0] at this
    exact this)
  have h2 := normDegree_le_of_metric_bounded_map K (HermitianBundle.standard K r) E ψ C b.equivFun.symm.injective hC0
    fun σ y => (hb σ y).2
  obtain ⟨s1, s2⟩ := standard_hermitian_bundle_semistable K r
  refine ⟨h1.2.trans ?_, ?_⟩
  · refine (add_le_add_left s1 _).trans ?_
    rw [zero_add]
  · have a := h1.1 ⊤
    have c := h2.1 ⊤
    have e1 : (⊤ : Submodule (𝓞 K) E.carrier).map φ = ⊤ := by
      rw [Submodule.map_top]; exact LinearMap.range_eq_top.mpr b.equivFun.surjective
    have e2 : (⊤ : Submodule (𝓞 K) (HermitianBundle.standard K r).carrier).map ψ = ⊤ := by
      rw [Submodule.map_top]; exact LinearMap.range_eq_top.mpr b.equivFun.symm.surjective
    have r1 : E.rank ⊤ = r := by
      rw [HermitianBundle.rank, finrank_top, Module.finrank_eq_card_basis b, Fintype.card_fin]
    have r2 : (HermitianBundle.standard K r).rank ⊤ = r := by
      rw [HermitianBundle.rank, finrank_top]
      exact Module.finrank_fin_fun (𝓞 K)
    rw [e1, s2, r1] at a
    rw [e2, s2, r2] at c
    rw [abs_le]
    constructor <;> linarith

end CoverDenseAlt
