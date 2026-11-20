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
Simplify using `[dTerm]`.
-/
theorem dTerm_zero (φ : I → E →+* ℂ) (k : ℕ) (z : I → ℂ) (x : E) :
    dTerm φ k 0 z x = ∏ i, (defCoord φ z x i)⁻¹ ^ k := by
  simp [dTerm]

/- English proof (translation)
Unfold `dTerm risingFactor`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [defCoord, Pi.zero_apply, zero_mul, add_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dTerm_origin (φ : I → E →+* ℂ) (k : ℕ) (m : I → ℕ) (x : E) :
    dTerm φ k m 0 x = risingFactor k m * ∏ i, ((φ i x)⁻¹ ^ (k + m i) * (starRingEnd ℂ (φ i x)) ^ m i) := by
  unfold dTerm risingFactor
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [defCoord, Pi.zero_apply, zero_mul, add_zero]
  ring

/- English proof (translation)
Simplify using `[dTerm, defCoord]`.
-/
example (φ : E →+* ℂ) (x : E) :
    dTerm (fun _ : Unit => φ) 4 (fun _ => 1) 0 x = -4 * (starRingEnd ℂ (φ x)) * (φ x)⁻¹ ^ 5 := by
  simp [dTerm, defCoord]

end GlobalTheory.DeformedSum
