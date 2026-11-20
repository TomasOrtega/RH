import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot

namespace GlobalTheory.TwV

open NumberField
open scoped Matrix

/- English proof (translation)
Use function extensionality and compare the values at `k`. Rewrite using `[← LinearMap.toMatrix'_mulVec f x]`. Simplify using `[Matrix.mulVec, dotProduct, map_sum]`.
-/
theorem map_apply_eq_mulVec {E K : Type} [Field E] [Field K] (ρ : E →+* K) {N n : ℕ}
    (f : (Fin N → E) →ₗ[E] (Fin n → E)) (x : Fin N → E) :
    (fun k => ρ (f x k)) = ((LinearMap.toMatrix' f).map ρ) *ᵥ (fun k => ρ (x k)) := by
  funext k
  rw [← LinearMap.toMatrix'_mulVec f x]
  simp [Matrix.mulVec, dotProduct, map_sum]

/- English proof (translation)
Unfold `locSp`. Rewrite using `[Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]`. Use `congr 1`. Use `Set.image_congr fun x _ => ?_` and prove the remaining obligations. Conclude with `map_apply_eq_mulVec ρ f x`.
-/
theorem locSp_map {E : Type} [Field E] [NumberField E] (W K : Type) [CommRing W] [Field K] [Algebra W K]
    (ρ : E →+* K) {N n : ℕ} (f : (Fin N → E) →ₗ[E] (Fin n → E)) (Λ : Submodule (𝓞 E) (Fin N → E)) :
    locSp W ρ (Λ.map (f.restrictScalars (𝓞 E))) =
      (locSp W ρ Λ).map ((((LinearMap.toMatrix' f).map ρ).mulVecLin).restrictScalars W) := by
  unfold locSp
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  exact map_apply_eq_mulVec ρ f x

end GlobalTheory.TwV
