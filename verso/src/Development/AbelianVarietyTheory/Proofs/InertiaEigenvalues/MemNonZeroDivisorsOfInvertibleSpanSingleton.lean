import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction. Treat this case separately.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.
-/
theorem invertible_eq_zero_of_smul_eq_zero {A : Type} [CommRing A] {M : Type} [AddCommGroup M]
    [Module A M] [Module.Invertible A M] (a : A) (h : ∀ m : M, a • m = 0) : a = 0 := by
  obtain ⟨t, ht⟩ := (Module.Invertible.bijective (R := A) (M := M)).2 1
  have hz : ∀ s : Module.Dual A M ⊗[A] M, a • s = 0 := by
    intro s
    induction s using TensorProduct.induction_on with
    | zero => exact smul_zero a
    | tmul f m => rw [← TensorProduct.tmul_smul, h m, TensorProduct.tmul_zero]
    | add x y hx hy => rw [smul_add, hx, hy, add_zero]
  have : a = contractLeft A M (a • t) := by rw [map_smul, ht, smul_eq_mul, mul_one]
  rw [this, hz t, map_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Chain the equalities or inequalities of the calculation.
-/
theorem mem_nonZeroDivisors_of_invertible_span_singleton : ∀ (A : Type) [CommRing A] (d : A),
    Module.Invertible A ↥(Ideal.span {d}) → d ∈ nonZeroDivisors A := by
  intro A _ d hinv
  rw [mem_nonZeroDivisors_iff_right]
  intro a had
  apply invertible_eq_zero_of_smul_eq_zero (M := ↥(Ideal.span {d})) a
  rintro ⟨m, hm⟩
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hm
  ext
  simp only [Submodule.coe_smul, smul_eq_mul, ZeroMemClass.coe_zero]
  calc a * (c * d) = c * (a * d) := by ring
    _ = 0 := by rw [had, mul_zero]

end GlobalTheory.BSP
