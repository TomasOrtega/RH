import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv

open MvPolynomial GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional

/- English proof (translation)
Set `L : σ.IntertwiningMap ρ →ₗ[ℂ] invFun (ρ.dual.tprod σ)` to `{ toFun := fun f => ⟨TensorProduct.lift (LinearMap.lcomp ℂ ℂ f.toLinearMap), fun g x => by`. Proceed by induction on `x with`. Consider the case `zero => simp`. Consider the case `tmul ξ w`. Establish `h` using `LinearMap.congr_fun (f.isIntertwining' g) w`.

Simplify using `only [LinearMap.comp_apply] at h`. Simplify using `only [Representation.tprod_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul, LinearMap.lcomp_apply, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, h, Representation.inv_self_apply]`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]⟩`. Use the proof step `map_add' := fun f f' => Subtype.ext (TensorProduct.ext' fun ξ w => by`. Express the relevant statement in the definitionally equal form `ξ (f.toLinearMap w + f'.toLinearMap w) = ξ (f.toLinearMap w) + ξ (f'.toLinearMap w)`.

Conclude with `map_add _ _ _)`. Use the proof step `map_smul' := fun c f => Subtype.ext (TensorProduct.ext' fun ξ w => by`. Express the relevant statement in the definitionally equal form `ξ (c • f.toLinearMap w) = c • ξ (f.toLinearMap w)`. Conclude with `map_smul _ _ _) }`. Establish `hL : ∀ f ξ w, (L f).1 (ξ ⊗ₜ w) = ξ (f.toLinearMap w)` using `fun _ _ _ => rfl`.

Use `⟨(LinearEquiv.ofBijective L ⟨fun f f' h => ?_, fun l => ?_⟩).symm⟩` and prove the remaining obligations. Use `Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)` and prove the remaining obligations. Use `(Module.evalEquiv ℂ V).injective (LinearMap.ext fun ξ => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ξ _ = ξ _`. Rewrite using `[← hL, ← hL, h]`.

Set `φ : W →ₗ[ℂ] V` to `(Module.evalEquiv ℂ V).symm.toLinearMap ∘ₗ (TensorProduct.curry l.1).flip`. Establish `hφ : ∀ (ξ : Module.Dual ℂ V) w, ξ (φ w) = l.1 (ξ ⊗ₜ w)` using `fun ξ w => by`. Simplify using `[φ]`. Use `⟨⟨φ, fun g => LinearMap.ext fun w => ?_⟩, Subtype.ext (TensorProduct.ext' fun ξ w => hφ ξ w)⟩` and prove the remaining obligations. Use `(Module.evalEquiv ℂ V).injective (LinearMap.ext fun ξ => ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `ξ (φ (σ g w)) = (ξ ∘ₗ ρ g) (φ w)`. Rewrite using `[hφ, hφ, ← mem_invFun.1 l.2 g ((ξ ∘ₗ ρ g) ⊗ₜ w), Representation.tprod_apply, TensorProduct.map_tmul]`. Use `congr 2`. Use extensionality with `v`. Simplify using `[Module.Dual.transpose_apply]`.
-/
theorem nonempty_invFun_dual_tprod_equiv (G V W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (σ : Representation ℂ G W) :
    Nonempty (invFun (ρ.dual.tprod σ) ≃ₗ[ℂ] σ.IntertwiningMap ρ) := by
  let L : σ.IntertwiningMap ρ →ₗ[ℂ] invFun (ρ.dual.tprod σ) :=
    { toFun := fun f => ⟨TensorProduct.lift (LinearMap.lcomp ℂ ℂ f.toLinearMap), fun g x => by
        induction x with
        | zero => simp
        | tmul ξ w =>
          have h := LinearMap.congr_fun (f.isIntertwining' g) w
          simp only [LinearMap.comp_apply] at h
          simp only [Representation.tprod_apply, TensorProduct.map_tmul, TensorProduct.lift.tmul,
            LinearMap.lcomp_apply, Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, h,
            Representation.inv_self_apply]
        | add a b ha hb => simp only [map_add, ha, hb]⟩
      map_add' := fun f f' => Subtype.ext (TensorProduct.ext' fun ξ w => by
        change ξ (f.toLinearMap w + f'.toLinearMap w) = ξ (f.toLinearMap w) + ξ (f'.toLinearMap w)
        exact map_add _ _ _)
      map_smul' := fun c f => Subtype.ext (TensorProduct.ext' fun ξ w => by
        change ξ (c • f.toLinearMap w) = c • ξ (f.toLinearMap w)
        exact map_smul _ _ _) }
  have hL : ∀ f ξ w, (L f).1 (ξ ⊗ₜ w) = ξ (f.toLinearMap w) := fun _ _ _ => rfl
  refine ⟨(LinearEquiv.ofBijective L ⟨fun f f' h => ?_, fun l => ?_⟩).symm⟩
  · refine Representation.IntertwiningMap.ext (LinearMap.ext fun w => ?_)
    refine (Module.evalEquiv ℂ V).injective (LinearMap.ext fun ξ => ?_)
    change ξ _ = ξ _
    rw [← hL, ← hL, h]
  · let φ : W →ₗ[ℂ] V := (Module.evalEquiv ℂ V).symm.toLinearMap ∘ₗ (TensorProduct.curry l.1).flip
    have hφ : ∀ (ξ : Module.Dual ℂ V) w, ξ (φ w) = l.1 (ξ ⊗ₜ w) := fun ξ w => by
      simp [φ]
    refine ⟨⟨φ, fun g => LinearMap.ext fun w => ?_⟩, Subtype.ext (TensorProduct.ext' fun ξ w => hφ ξ w)⟩
    refine (Module.evalEquiv ℂ V).injective (LinearMap.ext fun ξ => ?_)
    change ξ (φ (σ g w)) = (ξ ∘ₗ ρ g) (φ w)
    rw [hφ, hφ, ← mem_invFun.1 l.2 g ((ξ ∘ₗ ρ g) ⊗ₜ w), Representation.tprod_apply, TensorProduct.map_tmul]
    congr 2
    ext v
    simp [Module.Dual.transpose_apply]

end GlobalTheory.OneFunctional
