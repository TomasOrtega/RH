import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.GardFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.ClFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.RopComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.IsOpenMapVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

/- English proof (translation)
Set `l : N →ₗ[ℂ] N` to `(LinearEquiv.ofInjective c hc).symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range c) (T ∘ₗ c) (fun v => hT v)`. Establish `hl : ∀ v, c (l v) = T (c v)` using `fun v => by`. Use `(LinearEquiv.ofInjective c hc).apply_symm_apply (LinearMap.codRestrict (LinearMap.range c) (T ∘ₗ c) (fun v => hT v) v)` as an intermediate fact. Conclude with `congrArg Subtype.val this`. Take `⟨g, hg⟩` from `LinearMap.exists_extend (N.subtype ∘ₗ l)`.

Use `⟨g, fun v => ?_⟩` and prove the remaining obligations. Establish `e : g v = (l v : M)` using `LinearMap.congr_fun hg v`. Use `⟨e ▸ (l v).2, ?_⟩` and prove the remaining obligations. Rewrite using `[← hl v]`. Use `congr 1`.

Conclude with `Subtype.ext e`.
-/
private theorem lift_of_inj {M H : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup H] [Module ℂ H]
    (N : Submodule ℂ M) (c : N →ₗ[ℂ] H) (hc : Function.Injective c) (T : H →ₗ[ℂ] H)
    (hT : ∀ v : N, ∃ w : N, c w = T (c v)) :
    ∃ T' : M →ₗ[ℂ] M, ∀ v : N, ∃ h : T' v ∈ N, c ⟨T' v, h⟩ = T (c v) := by
  let l : N →ₗ[ℂ] N := (LinearEquiv.ofInjective c hc).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range c) (T ∘ₗ c) (fun v => hT v)
  have hl : ∀ v, c (l v) = T (c v) := fun v => by
    have := (LinearEquiv.ofInjective c hc).apply_symm_apply
      (LinearMap.codRestrict (LinearMap.range c) (T ∘ₗ c) (fun v => hT v) v)
    exact congrArg Subtype.val this
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (N.subtype ∘ₗ l)
  refine ⟨g, fun v => ?_⟩
  have e : g v = (l v : M) := LinearMap.congr_fun hg v
  refine ⟨e ▸ (l v).2, ?_⟩
  rw [← hl v]
  congr 1
  exact Subtype.ext e

/- English proof (translation)
Introduce `E _ _ _ a ha μ _ _ T hT`. Establish `hG` using `gardFacts E a ha μ`. Take `⟨hlin, hinj, -, hrop⟩` from `clFacts E a μ`. Establish `hadd : ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, cl μ (φ + ψ) = cl μ φ + cl μ ψ` using `fun φ hφ ψ hψ => by`. Use `(hlin φ ψ 1 1 (hG φ hφ).2.1 (hG ψ hψ).2.1).2` as an intermediate fact.

Simplify `this` using `only [one_smul]`. Establish `hsm : ∀ (s : ℂ), ∀ φ ∈ gard μ, cl μ (s • φ) = s • cl μ φ` using `fun s φ hφ => by`. Use `(hlin φ φ s 0 (hG φ hφ).2.1 (hG φ hφ).2.1).2` as an intermediate fact. Simplify `this` using `only [zero_smul, add_zero]`. Set `c : gard μ →ₗ[ℂ] HL μ` to `{ toFun := fun v => cl μ v.1 map_add' := fun v w => hadd v.1 v.2 w.1 w.2 map_smul' := fun s v => hsm s v.1 v.2 }`.

Establish `hc : Function.Injective c`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Conclude with `Subtype.ext (hinj v.1 (hG v.1 v.2).1 (hG v.1 v.2).2.1 hv)`. Establish `key : ∀ φ ∈ gard μ, ∃ φ' ∈ gard μ, cl μ φ' = T (cl μ φ)`.

Introduce `φ hφ`. Proceed by induction on `hφ using Submodule.span_induction with`. Consider the case `mem φ h`. Take `⟨ψ, F, hψ, e⟩` from `h`. Establish `hcont : Continuous ψ.1` using `((testOps E a ψ).1 hψ.2).1`.

Establish `hint : Integrable (fun y => ψ.1 y⁻¹) μ` using `(hcont.comp continuous_inv).integrable_of_hasCompactSupport (hψ.1.comp_homeomorph (Homeomorph.inv (GA E a)))`. Use `⟨⟨cv ψ.1 (T F), cvSm E a μ ψ hψ (T F)⟩, Submodule.subset_span ⟨ψ, T F, hψ, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hrop ψ φ F hψ e, hrop ψ _ (T F) hψ rfl]`. Conclude with `(ropComm _ _ μ T hT _ hint F).symm`. Consider the case `zero`.

Establish `h0 : cl μ (0 : Sm E a) = 0` using `map_zero c`. Conclude with `⟨0, Submodule.zero_mem _, by rw [h0, map_zero]⟩`. Consider the case `add x y hx hy ihx ihy`. Take `⟨x', hx', ex⟩` from `ihx`. Take `⟨y', hy', ey⟩` from `ihy`.

Conclude with `⟨x' + y', Submodule.add_mem _ hx' hy', by`. Rewrite using `[hadd x' hx' y' hy', hadd x hx y hy, ex, ey, map_add]⟩`. Consider the case `smul s x hx ihx`. Take `⟨x', hx', ex⟩` from `ihx`. Conclude with `⟨s • x', Submodule.smul_mem _ s hx', by`.

Rewrite using `[hsm s x' hx', hsm s x hx, ex, map_smul]⟩`. Take `⟨T', h⟩` from `lift_of_inj (gard μ) c hc T.toLinearMap fun v => by`. Take `⟨w, hw, e⟩` from `key v.1 v.2`. Conclude with `⟨⟨w, hw⟩, e⟩`. Use `⟨T', fun φ hφ => ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `h ⟨φ, hφ⟩`. Conclude with `⟨h1, h2⟩`.
-/
theorem UpperTheory.V.Cj.H.opLift :
    UpperTheory.V.Cj.H.OpLift := by
  intro E _ _ _ a ha μ _ _ T hT
  have hG := gardFacts E a ha μ
  obtain ⟨hlin, hinj, -, hrop⟩ := clFacts E a μ
  have hadd : ∀ φ ∈ gard μ, ∀ ψ ∈ gard μ, cl μ (φ + ψ) = cl μ φ + cl μ ψ := fun φ hφ ψ hψ => by
    have := (hlin φ ψ 1 1 (hG φ hφ).2.1 (hG ψ hψ).2.1).2
    simpa only [one_smul] using this
  have hsm : ∀ (s : ℂ), ∀ φ ∈ gard μ, cl μ (s • φ) = s • cl μ φ := fun s φ hφ => by
    have := (hlin φ φ s 0 (hG φ hφ).2.1 (hG φ hφ).2.1).2
    simpa only [zero_smul, add_zero] using this
  let c : gard μ →ₗ[ℂ] HL μ :=
    { toFun := fun v => cl μ v.1
      map_add' := fun v w => hadd v.1 v.2 w.1 w.2
      map_smul' := fun s v => hsm s v.1 v.2 }
  have hc : Function.Injective c := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact Subtype.ext (hinj v.1 (hG v.1 v.2).1 (hG v.1 v.2).2.1 hv)
  have key : ∀ φ ∈ gard μ, ∃ φ' ∈ gard μ, cl μ φ' = T (cl μ φ) := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨ψ, F, hψ, e⟩ := h
      have hcont : Continuous ψ.1 := ((testOps E a ψ).1 hψ.2).1
      have hint : Integrable (fun y => ψ.1 y⁻¹) μ :=
        (hcont.comp continuous_inv).integrable_of_hasCompactSupport
          (hψ.1.comp_homeomorph (Homeomorph.inv (GA E a)))
      refine ⟨⟨cv ψ.1 (T F), cvSm E a μ ψ hψ (T F)⟩, Submodule.subset_span ⟨ψ, T F, hψ, rfl⟩, ?_⟩
      rw [hrop ψ φ F hψ e, hrop ψ _ (T F) hψ rfl]
      exact (ropComm _ _ μ T hT _ hint F).symm
    | zero =>
      have h0 : cl μ (0 : Sm E a) = 0 := map_zero c
      exact ⟨0, Submodule.zero_mem _, by rw [h0, map_zero]⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨x', hx', ex⟩ := ihx
      obtain ⟨y', hy', ey⟩ := ihy
      exact ⟨x' + y', Submodule.add_mem _ hx' hy', by
        rw [hadd x' hx' y' hy', hadd x hx y hy, ex, ey, map_add]⟩
    | smul s x hx ihx =>
      obtain ⟨x', hx', ex⟩ := ihx
      exact ⟨s • x', Submodule.smul_mem _ s hx', by
        rw [hsm s x' hx', hsm s x hx, ex, map_smul]⟩
  obtain ⟨T', h⟩ := lift_of_inj (gard μ) c hc T.toLinearMap fun v => by
    obtain ⟨w, hw, e⟩ := key v.1 v.2
    exact ⟨⟨w, hw⟩, e⟩
  refine ⟨T', fun φ hφ => ?_⟩
  obtain ⟨h1, h2⟩ := h ⟨φ, hφ⟩
  exact ⟨h1, h2⟩
