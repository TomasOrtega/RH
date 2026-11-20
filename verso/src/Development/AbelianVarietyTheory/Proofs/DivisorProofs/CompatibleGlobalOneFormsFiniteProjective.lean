import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstantStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

/- English proof (translation)
Introduce `R _ C _ F hF h0`. Take `⟨n, ⟨Φ⟩⟩` from `hF`. Take `⟨l, -, hl⟩` from `GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ`. Set `L : Glob1 F →ₗ[R] (Fin n → R)` to `LinearMap.pi l`. Set `S : (Fin n → R) →ₗ[R] Glob1 F` to `Fintype.linearCombination R Φ.w`.

Establish `hSL : S.comp L = LinearMap.id`. Use `LinearMap.ext fun w ↦ ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.id_apply, S, L, Fintype.linearCombination_apply, LinearMap.pi_apply]`. Conclude with `(hl w).symm`. Establish `hsurj : Function.Surjective S` using `fun w ↦ ⟨L w, by`.

Simplify using `using LinearMap.congr_fun hSL w⟩`. Conclude with `⟨Module.Finite.of_surjective S hsurj, Module.Projective.of_split L S hSL⟩`.
-/
theorem compatibleGlobalOneForms_finite_projective : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R),
    HasFrame F → CohomZeroIsConstants F → Module.Finite R (Glob1 F) ∧ Module.Projective R (Glob1 F) := by
  intro R _ C _ F hF h0
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨l, -, hl⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ
  let L : Glob1 F →ₗ[R] (Fin n → R) := LinearMap.pi l
  let S : (Fin n → R) →ₗ[R] Glob1 F := Fintype.linearCombination R Φ.w
  have hSL : S.comp L = LinearMap.id := by
    refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply, S, L, Fintype.linearCombination_apply, LinearMap.pi_apply]
    exact (hl w).symm
  have hsurj : Function.Surjective S := fun w ↦ ⟨L w, by
    simpa using LinearMap.congr_fun hSL w⟩
  exact ⟨Module.Finite.of_surjective S hsurj, Module.Projective.of_split L S hSL⟩

end GlobalTheory.AbCoh
