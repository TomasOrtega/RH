import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.CountStA
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

/- English proof (translation)
Introduce `K _ _ n h s`. Use `⟨h.posDef s n _ ?_, fun c => ?_⟩` and prove the remaining obligations. Establish `hb` using `(Pi.basisFun K (Fin n)).linearIndependent`. Establish `he : (⇑(Pi.basisFun K (Fin n)) : Fin n → Fin n → K) = fun i => Pi.single i 1`. Use function extensionality and compare the values at `i`.

Conclude with `Pi.basisFun_apply K (Fin n) i`. Rewrite `hb` using `[he]`. Then use the resulting hypothesis. Establish `hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → K)`. Use function extensionality and compare the values at `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`.

Establish `hx` using `h.form_expand s c (fun i => Pi.single i 1)`. Rewrite `hx` using `[← hc]`. Rewrite using `[hx, ReciprocityTheory.MultiplicativeHeights.hq]`. Use `congr 1`. Simplify using `only [dotProduct, Matrix.mulVec, Finset.mul_sum, ReciprocityTheory.MultiplicativeHeights.embVec, Pi.star_apply, Complex.star_def]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm`.
-/
theorem gram_stdBasis_posDef_and_hq :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (h : HermFam K (Fin n → K)) (s : K →+* ℂ), (h.gram s (fun i => Pi.single i 1) : Matrix (Fin n) (Fin n) ℂ).PosDef ∧ ∀ c, ReciprocityTheory.MultiplicativeHeights.hq (h.gram s (fun i => Pi.single i 1)) (ReciprocityTheory.MultiplicativeHeights.embVec s c) = (h.form s c c).re := by
  intro K _ _ n h s
  refine ⟨h.posDef s n _ ?_, fun c => ?_⟩
  · have hb := (Pi.basisFun K (Fin n)).linearIndependent
    have he : (⇑(Pi.basisFun K (Fin n)) : Fin n → Fin n → K) = fun i => Pi.single i 1 := by
      funext i; exact Pi.basisFun_apply K (Fin n) i
    rwa [he] at hb
  · have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → K) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    have hx := h.form_expand s c (fun i => Pi.single i 1)
    rw [← hc] at hx
    rw [hx, ReciprocityTheory.MultiplicativeHeights.hq]
    congr 1
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ReciprocityTheory.MultiplicativeHeights.embVec, Pi.star_apply,
      Complex.star_def]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

end GlobalTheory.LamF
