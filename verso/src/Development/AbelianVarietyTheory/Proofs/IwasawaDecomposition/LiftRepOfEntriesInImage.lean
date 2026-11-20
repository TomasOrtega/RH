import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `k L Γ _ _ _ f b τ h`. Use `choose pre hpre using h`. Establish `hinj : Function.Injective (f.mapMatrix : Matrix (Fin b) (Fin b) k →+* Matrix (Fin b) (Fin b) L)` using `Matrix.map_injective f.injective`. Establish `key : ∀ g, f.mapMatrix (Matrix.of (pre g)) = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L)`. Introduce `g`.

Use extensionality with `i j`. Simplify using `[RingHom.mapMatrix_apply, Matrix.map_apply, hpre]`. Set `m : Γ →* Matrix (Fin b) (Fin b) k` to `{ toFun := fun g => Matrix.of (pre g) map_one' := hinj (by rw [key, map_one, map_one]; rfl) map_mul' := fun x y => hinj (by rw [map_mul, key, key, key, map_mul]; rfl) }`. Use `⟨MonoidHom.toHomUnits m, ?_⟩` and prove the remaining obligations. Use extensionality with `g i j`.

Simplify using `only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]`. Rewrite using `[MonoidHom.coe_toHomUnits]`. Conclude with `congrFun (congrFun (key g) i) j`.
-/
theorem lift_rep_of_entries_in_image : ∀ {k L Γ : Type} [Field k] [Field L] [Group Γ] (f : k →+* L) {b : ℕ} (τ : Γ →* GL (Fin b) L), (∀ g i j, ∃ x, f x = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) i j) → ∃ σ : Γ →* GL (Fin b) k, mapRep f σ = τ := by
  intro k L Γ _ _ _ f b τ h
  choose pre hpre using h
  have hinj : Function.Injective (f.mapMatrix : Matrix (Fin b) (Fin b) k →+* Matrix (Fin b) (Fin b) L) :=
    Matrix.map_injective f.injective
  have key : ∀ g, f.mapMatrix (Matrix.of (pre g)) = ((τ g : GL (Fin b) L) : Matrix (Fin b) (Fin b) L) := by
    intro g; ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply, hpre]
  let m : Γ →* Matrix (Fin b) (Fin b) k :=
    { toFun := fun g => Matrix.of (pre g)
      map_one' := hinj (by rw [key, map_one, map_one]; rfl)
      map_mul' := fun x y => hinj (by rw [map_mul, key, key, key, map_mul]; rfl) }
  refine ⟨MonoidHom.toHomUnits m, ?_⟩
  ext g i j
  simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe]
  rw [MonoidHom.coe_toHomUnits]
  exact congrFun (congrFun (key g) i) j

end GlobalTheory
