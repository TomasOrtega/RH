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
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. A detailed English derivation is pending.
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
