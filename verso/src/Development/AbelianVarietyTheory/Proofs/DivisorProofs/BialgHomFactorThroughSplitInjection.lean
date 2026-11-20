import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `O _ A B D _ _ _ _ _ _ j ρ f hρ hf`. Establish `hjinj : Function.Injective j` using `fun x y h => by`. Use `congrArg ρ h` as an intermediate fact. Rewrite `this` using `[hρ, hρ]`. Then use the resulting hypothesis. Establish `hjg : ∀ d, j (ρ (f d)) = f d` using `fun d => by`.

Take `⟨b, hb⟩` from `hf d`. Rewrite using `[← hb, hρ]`. Establish `hmapinj : Function.Injective (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A))`. Establish `hid : (TensorProduct.map ρ ρ).comp (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) = LinearMap.id`. Apply `TensorProduct.ext'` to reduce the goal to its premises.

Introduce `x y`. Simplify using `[hρ]`. Introduce `x y h`. Use `congrArg (TensorProduct.map ρ ρ) h` as an intermediate fact. Simplify `this` using `[← LinearMap.comp_apply, hid]`.

Set `gl : D →ₗ[O] B` to `ρ ∘ₗ (f : D →ₗ[O] A)`. Establish `hgl : ∀ d, j (gl d) = f d` using `hjg`. Establish `hcomp : (j : B →ₗ[O] A) ∘ₗ gl = (f : D →ₗ[O] A)` using `LinearMap.ext hgl`. Use `⟨{ gl with counit_comp := ?_ map_comp_comul := ?_ map_one' := ?_ map_mul' := ?_ }, hgl⟩` and prove the remaining obligations. Use extensionality with `d`.

Simplify using `only [LinearMap.coe_comp, Function.comp_apply]`. Rewrite using `[← CoalgHomClass.counit_comp_apply j, hgl, CoalgHomClass.counit_comp_apply]`. Use extensionality with `d`. Apply `hmapinj` to reduce the goal to its premises. Use `show TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (TensorProduct.map gl gl (comul d)) = TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (comul (gl d))`.

Rewrite using `[CoalgHomClass.map_comp_comul_apply j, hgl, ← LinearMap.comp_apply, ← TensorProduct.map_comp, hcomp, CoalgHomClass.map_comp_comul_apply f]`. Apply `hjinj show j (gl 1) = j 1` to reduce the goal to its premises. Rewrite using `[hgl, map_one, map_one]`. Introduce `x y`. Apply `hjinj` to reduce the goal to its premises.

Use `show j (gl (x * y)) = j (gl x * gl y)`. Rewrite using `[hgl, map_mul, map_mul, hgl, hgl]`.
-/
theorem bialgHom_factor_through_split :
    ∀ (O : Type) [CommRing O] (A B D : Type) [CommRing A] [CommRing B] [CommRing D] [Bialgebra O A] [Bialgebra O B] [Bialgebra O D] (j : B →ₐc[O] A) (ρ : A →ₗ[O] B) (f : D →ₐc[O] A), (∀ b, ρ (j b) = b) → (∀ d, f d ∈ Set.range j) → ∃ g : D →ₐc[O] B, ∀ d, j (g d) = f d := by
  intro O _ A B D _ _ _ _ _ _ j ρ f hρ hf
  have hjinj : Function.Injective j := fun x y h => by
    have := congrArg ρ h; rwa [hρ, hρ] at this
  have hjg : ∀ d, j (ρ (f d)) = f d := fun d => by
    obtain ⟨b, hb⟩ := hf d; rw [← hb, hρ]
  have hmapinj : Function.Injective (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) := by
    have hid : (TensorProduct.map ρ ρ).comp (TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A)) = LinearMap.id := by
      apply TensorProduct.ext'
      intro x y
      simp [hρ]
    intro x y h
    have := congrArg (TensorProduct.map ρ ρ) h
    simpa [← LinearMap.comp_apply, hid] using this
  let gl : D →ₗ[O] B := ρ ∘ₗ (f : D →ₗ[O] A)
  have hgl : ∀ d, j (gl d) = f d := hjg
  have hcomp : (j : B →ₗ[O] A) ∘ₗ gl = (f : D →ₗ[O] A) := LinearMap.ext hgl
  refine ⟨{ gl with
    counit_comp := ?_
    map_comp_comul := ?_
    map_one' := ?_
    map_mul' := ?_ }, hgl⟩
  · ext d
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [← CoalgHomClass.counit_comp_apply j, hgl, CoalgHomClass.counit_comp_apply]
  · ext d
    apply hmapinj
    show TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (TensorProduct.map gl gl (comul d)) =
      TensorProduct.map (j : B →ₗ[O] A) (j : B →ₗ[O] A) (comul (gl d))
    rw [CoalgHomClass.map_comp_comul_apply j, hgl, ← LinearMap.comp_apply, ← TensorProduct.map_comp, hcomp,
      CoalgHomClass.map_comp_comul_apply f]
  · apply hjinj
    show j (gl 1) = j 1
    rw [hgl, map_one, map_one]
  · intro x y
    apply hjinj
    show j (gl (x * y)) = j (gl x * gl y)
    rw [hgl, map_mul, map_mul, hgl, hgl]

end GlobalTheory
