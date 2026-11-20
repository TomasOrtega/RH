import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.SigmaConstantAgrees
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.UnitaryInverseIdentity
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Closure
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.IntPSDerivativeOfLG

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.C

namespace Extra

section Kernel

variable {K : Type} [Field K] {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Kernel

end Extra

/- English proof (translation)
Introduce `K _ _ R l linv ph a b hl hu h0 h3 hN h2 hAdj hinv hab`. Use `jetExp' K R l linv ph hl h0 ?_` and prove the remaining obligations. Introduce `i hi`. Break down `Nat.lt_or_ge i 3 with h | h` into its components or cases. Establish `: i = 1 ∨ i = 2` using `by omega`.

Break down `this with rfl | rfl` into its components or cases. Conclude with `jetOne' K R l linv ph hl hu h0 hN h2`. Establish `e` using `R.mul_mem hinv (jetAdjoint' K R l linv ph a b hl h0 hAdj)`. Rewrite `e` using `[← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.2 hab), one_mul]`. Then use the resulting hypothesis. Conclude with `h3 i h`.
-/
theorem all_jets_integral : JetsAll := by
  intro K _ _ R l linv ph a b hl hu h0 h3 hN h2 hAdj hinv hab
  refine jetExp' K R l linv ph hl h0 ?_
  intro i hi
  rcases Nat.lt_or_ge i 3 with h | h
  · have : i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl
    · exact jetOne' K R l linv ph hl hu h0 hN h2
    · have e := R.mul_mem hinv (jetAdjoint' K R l linv ph a b hl h0 hAdj)
      rwa [← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.2 hab), one_mul] at e
  · exact h3 i h

end Formalism.L2.Th1.C
