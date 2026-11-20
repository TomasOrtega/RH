import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

/- English proof (translation)
Take `⟨t, ht⟩` from `(Module.Invertible.bijective (R := A) (M := M)).2 1`. Establish `hz : ∀ s : Module.Dual A M ⊗[A] M, a • s = 0`. Introduce `s`. Proceed by induction on `s using TensorProduct.induction_on with`. Consider the case `zero => exact smul_zero a`.

Consider the case `tmul f m => rw [← TensorProduct.tmul_smul, h m, TensorProduct.tmul_zero]`. Consider the case `add x y hx hy => rw [smul_add, hx, hy, add_zero]`. Establish `: a = contractLeft A M (a • t)` using `by rw [map_smul, ht, smul_eq_mul, mul_one]`. Rewrite using `[this, hz t, map_zero]`.
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
Introduce `A _ d hinv`. Rewrite using `[mem_nonZeroDivisors_iff_right]`. Introduce `a had`. Apply `invertible_eq_zero_of_smul_eq_zero (M := ↥(Ideal.span {d})) a` to reduce the goal to its premises. Introduce and unpack `⟨m, hm⟩`.

Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hm`. Use `ext`. Simplify using `only [Submodule.coe_smul, smul_eq_mul, ZeroMemClass.coe_zero]`. Combine the equalities or inequalities in the displayed calculation.
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
