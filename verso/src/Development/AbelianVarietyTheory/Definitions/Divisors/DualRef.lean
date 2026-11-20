import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualRef

set_option autoImplicit false

namespace GlobalTheory.Mean4O

/- English proof (translation)
Introduce `c σ _ _ _ hf` and use `h.referenceMetric_mul_dual_eq_one c σ _ hf`.
-/
theorem Setup.Core.dualRef {D : Formalism.BasicNotions.D7} {O : Setup D} (h : O.Core) : O.DualRef :=
  fun c σ _ _ _ hf => h.referenceMetric_mul_dual_eq_one c σ _ hf

end GlobalTheory.Mean4O
