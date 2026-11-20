import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates

noncomputable section

open NumberField GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates

namespace GlobalTheory.DeformedSum

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def dTerm (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (z : I → ℂ) (x : E) : ℂ :=
  ∏ i, (((-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), ((k : ℂ) + j)) * (starRingEnd ℂ (φ i x)) ^ m i *
    (defCoord φ z x i)⁻¹ ^ (k + m i))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem dTerm_zero (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (x : E) :
    dTerm φ k 0 z x = ∏ i, (defCoord φ z x i)⁻¹ ^ k := by
  simp [dTerm]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dTerm_origin (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E) :
    dTerm φ k m 0 x = risingFactor k m * ∏ i, ((φ i x)⁻¹ ^ (k + m i) * (starRingEnd ℂ (φ i x)) ^ m i) := by
  unfold dTerm risingFactor
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [defCoord, Pi.zero_apply, zero_mul, add_zero]
  ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
example (φ : E →+* ℂ) (x : E) :
    dTerm (fun _ : Unit => φ) 4 (fun _ => 1) 0 x = -4 * (starRingEnd ℂ (φ x)) * (φ x)⁻¹ ^ 5 := by
  simp [dTerm, defCoord]

end GlobalTheory.DeformedSum
