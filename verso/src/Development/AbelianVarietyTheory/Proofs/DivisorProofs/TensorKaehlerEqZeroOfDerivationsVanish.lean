import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RedHomAlgebraMap
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Introduce `R B C _ _ _ _ _ hP z hz`. Take `⟨s, hs⟩` from `(Module.projective_def' (R := C) (P := Ω[C⁄R])).1 hP`. Set `π : (Ω[C⁄R] →₀ C) →ₗ[C] Ω[C⁄R]` to `Finsupp.linearCombination C id`. Establish `hcomp : (LinearMap.lTensor B (π.restrictScalars R)) ∘ₗ (LinearMap.lTensor B (s.restrictScalars R)) = LinearMap.id`. Rewrite using `[← LinearMap.lTensor_comp]`.

Establish `: (π.restrictScalars R) ∘ₗ (s.restrictScalars R) = LinearMap.id`. Conclude with `LinearMap.ext fun x => LinearMap.congr_fun hs x`. Rewrite using `[this, LinearMap.lTensor_id]`. Establish `key : LinearMap.lTensor B (s.restrictScalars R) z = 0`. Apply `(TensorProduct.finsuppRight R R B C Ω[C⁄R]).injective` to reduce the goal to its premises.

Rewrite using `[map_zero]`. Use extensionality with `i`. Set `θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C` to `(Algebra.TensorProduct.includeRight (R := R) (A := B) (B := C)).toLinearMap ∘ₗ ((Finsupp.lapply (R := C) (M := C) i).restrictScalars R ∘ₗ s.restrictScalars R)`. Establish `hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x`. Introduce `c x`.

Simplify using `[θ, Algebra.TensorProduct.tmul_mul_tmul]`. Establish `h1` using `hz θ hθ`. Establish `heq : ∀ w : B ⊗[R] Ω[C⁄R], (TensorProduct.finsuppRight R R B C Ω[C⁄R] (LinearMap.lTensor B (s.restrictScalars R) w)) i = LinearMap.liftBaseChange B θ w`. Introduce `w`. Proceed by induction on `w using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul b x`. Simplify using `[θ, TensorProduct.finsuppRight_apply_tmul_apply, LinearMap.liftBaseChange_tmul, TensorProduct.smul_tmul']`. Consider the case `add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]`. Rewrite using `[heq, h1]`.

Both sides reduce to the same expression. Use `congrArg (fun f => f z) hcomp` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply] at this`. Rewrite using `[← this, key, map_zero]`.
-/
theorem tensor_kaehler_eq_zero_of_derivations_vanish :
  ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C], Module.Projective C Ω[C⁄R] → ∀ z : B ⊗[R] Ω[C⁄R], (∀ θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C, (∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) → LinearMap.liftBaseChange B θ z = 0) → z = 0 := by
  intro R B C _ _ _ _ _ hP z hz
  classical
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := C) (P := Ω[C⁄R])).1 hP
  let π : (Ω[C⁄R] →₀ C) →ₗ[C] Ω[C⁄R] := Finsupp.linearCombination C id
  have hcomp : (LinearMap.lTensor B (π.restrictScalars R)) ∘ₗ (LinearMap.lTensor B (s.restrictScalars R))
      = LinearMap.id := by
    rw [← LinearMap.lTensor_comp]
    have : (π.restrictScalars R) ∘ₗ (s.restrictScalars R) = LinearMap.id := by
      exact LinearMap.ext fun x => LinearMap.congr_fun hs x
    rw [this, LinearMap.lTensor_id]
  have key : LinearMap.lTensor B (s.restrictScalars R) z = 0 := by
    apply (TensorProduct.finsuppRight R R B C Ω[C⁄R]).injective
    rw [map_zero]
    ext i
    let θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C :=
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := C)).toLinearMap ∘ₗ
        ((Finsupp.lapply (R := C) (M := C) i).restrictScalars R ∘ₗ s.restrictScalars R)
    have hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x := by
      intro c x
      simp [θ, Algebra.TensorProduct.tmul_mul_tmul]
    have h1 := hz θ hθ
    have heq : ∀ w : B ⊗[R] Ω[C⁄R], (TensorProduct.finsuppRight R R B C Ω[C⁄R]
        (LinearMap.lTensor B (s.restrictScalars R) w)) i = LinearMap.liftBaseChange B θ w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
        simp [θ, TensorProduct.finsuppRight_apply_tmul_apply, LinearMap.liftBaseChange_tmul,
          TensorProduct.smul_tmul']
      | add u v hu hv => simp only [map_add, Finsupp.add_apply, hu, hv]
    rw [heq, h1]; rfl
  have := congrArg (fun f => f z) hcomp
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  rw [← this, key, map_zero]

end GlobalTheory
