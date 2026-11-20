import Mathlib
import GroundTheory.AutomorphicForms.GKModules.GKModule

noncomputable section

namespace GroundTheory.Automorphic

namespace CompactRep

open MeasureTheory Module Set

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
  {σ : Representation ℂ K W}

/- English proof (translation)
Use `borelize K`. Set `K₀ : TopologicalSpace.PositiveCompacts K` to `⟨⟨univ, isCompact_univ⟩, by simp [interior_univ]⟩`. Use `set μ : Measure K := Measure.haarMeasure K₀`. Establish `hμ1 : μ univ = 1`. Use `Measure.haarMeasure_self (K₀ := K₀)` as an intermediate fact.

Simplify `this` using `[K₀]`. Use `haveI : IsProbabilityMeasure μ := ⟨hμ1⟩`. Use `set d := finrank ℂ W`. Set `b` to `Module.finBasis ℂ W`. Set `e : W ≃ₗ[ℂ] (Fin d → ℂ)` to `b.equivFun`.

Set `S : K → ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))` to `fun k => LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ σ k ∘ₗ e.symm.toLinearMap)`. Establish `hSapply : ∀ k w, S k (e w) = e (σ k w)` using `fun k w => by`. Simplify using `[S]`. Establish `hSmul : ∀ a c, S (a * c) = (S a).comp (S c)` using `fun a c => by`. Use extensionality with `x : 1`.

Simplify using `[S, map_mul]`. Establish `hS : Continuous S`. Use `continuous_clm_apply.2 fun y => continuous_pi fun i => ?_` and prove the remaining obligations. Use `hσ (b.coord i) (e.symm y)` as an intermediate fact. Use `this.congr fun k => ?_` and prove the remaining obligations.

Simplify using `[S, e, Basis.equivFun_apply, Basis.coord_apply]`. Take `⟨C₀, hC₀⟩` from `U.exists_isCompl`. Set `p : W →ₗ[ℂ] W` to `U.subtype ∘ₗ Submodule.projectionOnto U C₀ hC₀`. Establish `hpU : ∀ u ∈ U, p u = u` using `fun u hu => by show ((Submodule.projectionOnto U C₀ hC₀ u : U) : W) = u`. Rewrite using `[Submodule.projectionOnto_apply_of_mem_left _ hu]`.

Establish `hpmem : ∀ w, p w ∈ U` using `fun w => Subtype.prop _`. Set `P₀ : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)` to `LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ p ∘ₗ e.symm.toLinearMap)`. Establish `hP₀ : ∀ w, P₀ (e w) = e (p w)` using `fun w => by simp [P₀]`. Set `f : K → ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ))` to `fun k => (S k).comp (P₀.comp (S k⁻¹))`. Establish `hf : Continuous f` using `hS.clm_comp (continuous_const.clm_comp (hS.comp continuous_inv))`.

Establish `hfi : Integrable f μ` using `hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Establish `hfx : ∀ x, Integrable (fun k => f k x) μ` using `fun x => (hf.clm_apply continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`. Establish `hfapply : ∀ k w, f k (e w) = e (σ k (p (σ k⁻¹ w)))` using `fun k w => by`. Simplify using `only [f, ContinuousLinearMap.comp_apply, hSapply, hP₀]`. Use `set P := ∫ k, f k ∂μ`.

Establish `hPU : ∀ u ∈ U, P (e u) = e u`. Introduce `u hu`. Rewrite using `[ContinuousLinearMap.integral_apply hfi]`. Establish `: ∀ k, f k (e u) = e u` using `fun k => by`. Rewrite using `[hfapply, hpU _ (hU _ _ hu), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.

Simplify using `only [this, integral_const]`. Rewrite using `[show μ.real univ = 1 by simp [Measure.real, hμ1], one_smul]`. Set `R : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)` to `LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ (LinearMap.id - p) ∘ₗ e.symm.toLinearMap)`. Establish `hPmem : ∀ w, e.symm (P (e w)) ∈ U`. Introduce `w`.

Establish `h1 : R (P (e w)) = 0`. Rewrite using `[ContinuousLinearMap.integral_apply hfi, ← ContinuousLinearMap.integral_comp_comm _ (hfx _)]`. Establish `: ∀ k, R (f k (e w)) = 0` using `fun k => by`. Rewrite using `[hfapply]`. Simplify using `only [R, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply, LinearMap.sub_apply, LinearMap.id_apply, hpU _ (hU _ _ (hpmem _)), sub_self, map_zero]`.

Simplify using `[this]`. Establish `h2 : e.symm (P (e w)) - p (e.symm (P (e w))) = 0`. Use `congrArg e.symm h1` as an intermediate fact. Simplify `this` using `[R]`. Rewrite `h2` using `[sub_eq_zero]`.

Rewrite using `[h2]`. Conclude with `hpmem _`. Establish `hPcomm : ∀ g x, P (S g x) = S g (P x)`. Introduce `g x`. Rewrite using `[ContinuousLinearMap.integral_apply hfi, ContinuousLinearMap.integral_apply hfi, ← ContinuousLinearMap.integral_comp_comm _ (hfx _)]`.

Establish `h1 : ∀ k, f k (S g x) = S k (P₀ (S (k⁻¹ * g) x))`. Introduce `k`. Rewrite using `[hSmul]`. Both sides reduce to the same expression. Establish `h2 : ∀ k, S g (f k x) = S (g * k) (P₀ (S ((g * k)⁻¹ * g) x))`.

Introduce `k`. Rewrite using `[hSmul g k, show (g * k)⁻¹ * g = k⁻¹ by group]`. Both sides reduce to the same expression. Simplify using `only [h1, h2]`. Conclude with `(integral_mul_left_eq_self (μ := μ) (fun y => S y (P₀ (S (y⁻¹ * g) x))) g).symm`.

Set `Q : W →ₗ[ℂ] U` to `LinearMap.codRestrict U (e.symm.toLinearMap ∘ₗ P.toLinearMap ∘ₗ e.toLinearMap) fun w => hPmem w`. Establish `hQ : ∀ x : U, Q x = x` using `fun x => Subtype.ext (by`. Simplify using `[Q, hPU _ x.2])`. Use `⟨LinearMap.ker Q, LinearMap.isCompl_of_proj hQ, fun k c hc => ?_⟩` and prove the remaining obligations. Rewrite `hc`, the goal using `[LinearMap.mem_ker]`.

Establish `hc' : P (e c) = 0`. Use `congrArg (fun y : U => e (y : W)) hc` as an intermediate fact. Simplify `this` using `[Q]`. Use `Subtype.ext ?_` and prove the remaining obligations. Simplify using `only [Q, LinearMap.codRestrict_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, ContinuousLinearMap.coe_coe, ZeroMemClass.coe_zero]`.

Rewrite using `[← hSapply, hPcomm, hc', map_zero, map_zero]`.
-/
theorem exists_isCompl_stable (hσ : Representation.HasContinuousCoeff σ) (U : Submodule ℂ W)
    (hU : ∀ k, ∀ u ∈ U, σ k u ∈ U) :
    ∃ C : Submodule ℂ W, IsCompl U C ∧ ∀ k, ∀ c ∈ C, σ k c ∈ C := by
  classical
  borelize K
  let K₀ : TopologicalSpace.PositiveCompacts K :=
    ⟨⟨univ, isCompact_univ⟩, by simp [interior_univ]⟩
  set μ : Measure K := Measure.haarMeasure K₀
  have hμ1 : μ univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := K₀)
    simpa [K₀] using this
  haveI : IsProbabilityMeasure μ := ⟨hμ1⟩
  set d := finrank ℂ W
  let b := Module.finBasis ℂ W
  let e : W ≃ₗ[ℂ] (Fin d → ℂ) := b.equivFun

  let S : K → ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) := fun k =>
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ σ k ∘ₗ e.symm.toLinearMap)
  have hSapply : ∀ k w, S k (e w) = e (σ k w) := fun k w => by
    simp [S]
  have hSmul : ∀ a c, S (a * c) = (S a).comp (S c) := fun a c => by
    ext x : 1
    simp [S, map_mul]
  have hS : Continuous S := by
    refine continuous_clm_apply.2 fun y => continuous_pi fun i => ?_
    have := hσ (b.coord i) (e.symm y)
    refine this.congr fun k => ?_
    simp [S, e, Basis.equivFun_apply, Basis.coord_apply]

  obtain ⟨C₀, hC₀⟩ := U.exists_isCompl
  let p : W →ₗ[ℂ] W := U.subtype ∘ₗ Submodule.projectionOnto U C₀ hC₀
  have hpU : ∀ u ∈ U, p u = u := fun u hu => by
    show ((Submodule.projectionOnto U C₀ hC₀ u : U) : W) = u
    rw [Submodule.projectionOnto_apply_of_mem_left _ hu]
  have hpmem : ∀ w, p w ∈ U := fun w => Subtype.prop _
  let P₀ : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ p ∘ₗ e.symm.toLinearMap)
  have hP₀ : ∀ w, P₀ (e w) = e (p w) := fun w => by simp [P₀]
  let f : K → ((Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) := fun k => (S k).comp (P₀.comp (S k⁻¹))
  have hf : Continuous f := hS.clm_comp (continuous_const.clm_comp (hS.comp continuous_inv))
  have hfi : Integrable f μ :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfx : ∀ x, Integrable (fun k => f k x) μ := fun x =>
    (hf.clm_apply continuous_const).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfapply : ∀ k w, f k (e w) = e (σ k (p (σ k⁻¹ w))) := fun k w => by
    simp only [f, ContinuousLinearMap.comp_apply, hSapply, hP₀]
  set P := ∫ k, f k ∂μ

  have hPU : ∀ u ∈ U, P (e u) = e u := by
    intro u hu
    rw [ContinuousLinearMap.integral_apply hfi]
    have : ∀ k, f k (e u) = e u := fun k => by
      rw [hfapply, hpU _ (hU _ _ hu), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]
    simp only [this, integral_const]
    rw [show μ.real univ = 1 by simp [Measure.real, hμ1], one_smul]

  let R : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ) :=
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ (LinearMap.id - p) ∘ₗ e.symm.toLinearMap)
  have hPmem : ∀ w, e.symm (P (e w)) ∈ U := by
    intro w
    have h1 : R (P (e w)) = 0 := by
      rw [ContinuousLinearMap.integral_apply hfi, ← ContinuousLinearMap.integral_comp_comm _ (hfx _)]
      have : ∀ k, R (f k (e w)) = 0 := fun k => by
        rw [hfapply]
        simp only [R, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_comp,
          LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.symm_apply_apply, LinearMap.sub_apply,
          LinearMap.id_apply, hpU _ (hU _ _ (hpmem _)), sub_self, map_zero]
      simp [this]
    have h2 : e.symm (P (e w)) - p (e.symm (P (e w))) = 0 := by
      have := congrArg e.symm h1
      simpa [R] using this
    rw [sub_eq_zero] at h2
    rw [h2]
    exact hpmem _

  have hPcomm : ∀ g x, P (S g x) = S g (P x) := by
    intro g x
    rw [ContinuousLinearMap.integral_apply hfi, ContinuousLinearMap.integral_apply hfi,
      ← ContinuousLinearMap.integral_comp_comm _ (hfx _)]
    have h1 : ∀ k, f k (S g x) = S k (P₀ (S (k⁻¹ * g) x)) := by
      intro k
      rw [hSmul]
      rfl
    have h2 : ∀ k, S g (f k x) = S (g * k) (P₀ (S ((g * k)⁻¹ * g) x)) := by
      intro k
      rw [hSmul g k, show (g * k)⁻¹ * g = k⁻¹ by group]
      rfl
    simp only [h1, h2]
    exact (integral_mul_left_eq_self (μ := μ) (fun y => S y (P₀ (S (y⁻¹ * g) x))) g).symm

  let Q : W →ₗ[ℂ] U := LinearMap.codRestrict U
    (e.symm.toLinearMap ∘ₗ P.toLinearMap ∘ₗ e.toLinearMap) fun w => hPmem w
  have hQ : ∀ x : U, Q x = x := fun x => Subtype.ext (by
    simp [Q, hPU _ x.2])
  refine ⟨LinearMap.ker Q, LinearMap.isCompl_of_proj hQ, fun k c hc => ?_⟩
  rw [LinearMap.mem_ker] at hc ⊢
  have hc' : P (e c) = 0 := by
    have := congrArg (fun y : U => e (y : W)) hc
    simpa [Q] using this
  refine Subtype.ext ?_
  simp only [Q, LinearMap.codRestrict_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, ContinuousLinearMap.coe_coe, ZeroMemClass.coe_zero]
  rw [← hSapply, hPcomm, hc', map_zero, map_zero]

end CompactRep

end GroundTheory.Automorphic
