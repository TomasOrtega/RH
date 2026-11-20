import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyEndCharpolySpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativePolynomialFunctionEqNormFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

/- English proof (translation)
Introduce `K _ A f Ω _ _ _ R`. Take `⟨⟨hm, hd, hev⟩, -⟩` from `GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f`. Use `GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm Ω A.dim (fun F => (deg (A := A) (B := A) (Polynomial.aeval f F) : ℚ)) ((charpoly f).map (Int.castRingHom ℚ)) ?_ ?_ ?_ ?_ ?_ R` and prove the remaining obligations. Introduce `F G`. Establish `h` using `(isIsogeny_comp_iff_and_deg_comp K A A A (Polynomial.aeval f G) (Polynomial.aeval f F) rfl rfl).2`.

Establish `e : Polynomial.aeval f (F * G) = Polynomial.aeval f G ≫ Polynomial.aeval f F`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Rewrite using `[e, h]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Introduce `n u`. Take `⟨Φ, hΦ, hΦev⟩` from `GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl n (fun i => Polynomial.aeval f (u i))`. Use `⟨Φ, hΦ, fun m => ?_⟩` and prove the remaining obligations. Rewrite using `[hΦev m]`.

Simplify using `only [map_sum, map_zsmul]`. Conclude with `hm.map _`. Rewrite using `[Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]`. Conclude with `hd`. Introduce `n`.

Rewrite using `[Polynomial.eval_intCast_map, Int.cast_id, hev n]`. Establish `e : Polynomial.aeval f (Polynomial.C n - Polynomial.X) = ((n : End A) - f)`. Rewrite using `[map_sub, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast]`. Simplify using `only [e]`. Use `push_cast`.

Both sides reduce to the same expression.
-/
theorem deg_aeval_eq_prod_aroots : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (R : Polynomial ℤ), algebraMap ℚ Ω (deg (A := A) (B := A) (Polynomial.aeval f R) : ℚ) = ((((charpoly f).map (Int.castRingHom ℚ)).aroots Ω).map (fun a => Polynomial.aeval a R)).prod := by
  intro K _ A f Ω _ _ _ R
  obtain ⟨⟨hm, hd, hev⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec K A f
  refine GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm Ω A.dim (fun F => (deg (A := A) (B := A) (Polynomial.aeval f F) : ℚ))
    ((charpoly f).map (Int.castRingHom ℚ)) ?_ ?_ ?_ ?_ ?_ R
  · intro F G
    have h := (isIsogeny_comp_iff_and_deg_comp K A A A (Polynomial.aeval f G) (Polynomial.aeval f F) rfl rfl).2
    have e : Polynomial.aeval f (F * G) = Polynomial.aeval f G ≫ Polynomial.aeval f F := by
      rw [map_mul]; rfl
    rw [e, h]
    push_cast
    ring
  · intro n u
    obtain ⟨Φ, hΦ, hΦev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl n (fun i => Polynomial.aeval f (u i))
    refine ⟨Φ, hΦ, fun m => ?_⟩
    rw [hΦev m]
    simp only [map_sum, map_zsmul]
  · exact hm.map _
  · rw [Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int _)]
    exact hd
  · intro n
    rw [Polynomial.eval_intCast_map, Int.cast_id, hev n]
    have e : Polynomial.aeval f (Polynomial.C n - Polynomial.X) = ((n : End A) - f) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, eq_intCast]
    simp only [e]
    push_cast
    rfl

end GlobalTheory.AV.AbVar
