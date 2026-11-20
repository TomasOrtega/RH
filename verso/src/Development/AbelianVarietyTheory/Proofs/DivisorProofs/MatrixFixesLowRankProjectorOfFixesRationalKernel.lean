import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbUnitary
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.RatFix

/- English proof (translation)
Use `set ι : E →+* R ⊗[F] E := inclR (F := F) R with hι`. Establish `hN : (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) - A₀.map ι * B₀.map ι = (1 - A₀ * B₀).map ι`. Rewrite using `[Matrix.map_sub _ (map_sub ι), Matrix.map_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]`. Rewrite using `[hN]`. Establish `hBN : B₀ * (1 - A₀ * B₀) = 0`.

Rewrite using `[Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBA, Matrix.one_mul, sub_self]`. Use extensionality with `i j`. Establish `hv : B₀.mulVec (fun k => ((1 : Matrix (Fin M) (Fin M) E) - A₀ * B₀) k j) = 0`. Use function extensionality and compare the values at `a`. Use `congrFun (congrFun hBN a) j` as an intermediate fact.

Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`. Use `congrFun (hG _ hv) i` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`.
-/
theorem ratfix_mul_eq (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E) (hBA : B₀ * A₀ = 1) (G : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (hG : ∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) :
    G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) := by
  set ι : E →+* R ⊗[F] E := inclR (F := F) R with hι
  have hN : (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) - A₀.map ι * B₀.map ι = (1 - A₀ * B₀).map ι := by
    rw [Matrix.map_sub _ (map_sub ι), Matrix.map_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]
  rw [hN]
  have hBN : B₀ * (1 - A₀ * B₀) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBA, Matrix.one_mul, sub_self]
  ext i j
  have hv : B₀.mulVec (fun k => ((1 : Matrix (Fin M) (Fin M) E) - A₀ * B₀) k j) = 0 := by
    funext a
    have := congrFun (congrFun hBN a) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have := congrFun (hG _ hv) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

/- English proof (translation)
Introduce `F E _ _ _ R _ _ M A₀ B₀ hBA G hG` and use `ratfix_mul_eq F E R M A₀ B₀ hBA G hG`.
-/
theorem ratfix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E), B₀ * A₀ = 1 → ∀ G : Matrix (Fin M) (Fin M) (R ⊗[F] E), (∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) → G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) :=
  fun F E _ _ _ R _ _ M A₀ B₀ hBA G hG => ratfix_mul_eq F E R M A₀ B₀ hBA G hG

end GlobalTheory.RatFix
