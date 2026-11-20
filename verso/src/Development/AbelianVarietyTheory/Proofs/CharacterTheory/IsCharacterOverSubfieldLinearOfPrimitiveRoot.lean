import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
namespace GlobalTheory.BI

/- English proof (translation)
Introduce `K L _ _ _ G _ m ζ lam hm hζ hG`. Use `haveI : NeZero m := ⟨hm⟩`. Establish `hinj : Function.Injective (algebraMap K L)` using `(algebraMap K L).injective`. Establish `hζ' : IsPrimitiveRoot (algebraMap K L ζ) m` using `hζ.map_of_injective hinj`. Establish `h : ∀ g : G, ∃ x : K, algebraMap K L x = (lam g : L)`.

Introduce `g`. Establish `h1 : (lam g : L) ^ m = 1`. Rewrite using `[← Units.val_pow_eq_pow_val, ← map_pow, hG, map_one, Units.val_one]`. Take `⟨i, -, hi⟩` from `hζ'.eq_pow_of_pow_eq_one h1`. Conclude with `⟨ζ ^ i, by rw [map_pow, hi]⟩`.

Use `choose μ hμ using h`. Set `μ' : G →* K` to `{ toFun := μ map_one' := hinj (by rw [hμ]; simp) map_mul' := fun a b => hinj (by rw [map_mul (algebraMap K L), hμ, hμ, hμ]; simp) }`. Use `⟨1, ((algebraMap K (Module.End K (Fin 1 → K))).toMonoidHom).comp μ', fun g => ?_⟩` and prove the remaining obligations. Establish `: Representation.character (((algebraMap K (Module.End K (Fin 1 → K))).toMonoidHom).comp μ' : Representation K G (Fin 1 → K)) g = μ g`. Express the relevant statement in the definitionally equal form `LinearMap.trace K (Fin 1 → K) (algebraMap K (Module.End K (Fin 1 → K)) (μ g)) = μ g`.

Rewrite using `[Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one]`. Simplify using the standard rewrite rules. Rewrite using `[this, hμ]`.
-/
theorem isChar_linear : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G] (m : ℕ) (ζ : K) (lam : G →* Lˣ), m ≠ 0 → IsPrimitiveRoot ζ m → (∀ g : G, g ^ m = 1) → IsChar K L (fun g => (lam g : L)) := by
  intro K L _ _ _ G _ m ζ lam hm hζ hG
  haveI : NeZero m := ⟨hm⟩
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hζ' : IsPrimitiveRoot (algebraMap K L ζ) m := hζ.map_of_injective hinj
  have h : ∀ g : G, ∃ x : K, algebraMap K L x = (lam g : L) := by
    intro g
    have h1 : (lam g : L) ^ m = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hG, map_one, Units.val_one]
    obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one h1
    exact ⟨ζ ^ i, by rw [map_pow, hi]⟩
  choose μ hμ using h
  let μ' : G →* K :=
    { toFun := μ
      map_one' := hinj (by rw [hμ]; simp)
      map_mul' := fun a b => hinj (by rw [map_mul (algebraMap K L), hμ, hμ, hμ]; simp) }
  refine ⟨1, ((algebraMap K (Module.End K (Fin 1 → K))).toMonoidHom).comp μ', fun g => ?_⟩
  have : Representation.character (((algebraMap K (Module.End K (Fin 1 → K))).toMonoidHom).comp μ' : Representation K G (Fin 1 → K)) g = μ g := by
    change LinearMap.trace K (Fin 1 → K) (algebraMap K (Module.End K (Fin 1 → K)) (μ g)) = μ g
    rw [Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one]
    simp
  rw [this, hμ]
end GlobalTheory.BI
