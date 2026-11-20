import Formalism.JumpKernelCokernel.Statement
import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.TruncZero

namespace Formalism.KernelCokernelLengths

/- English proof (translation)
Introduce `R _ u π₀ q ℓ h η y hℓ hη hy`. Apply `Formalism.TruncatedSeriesCounting.R9.pow_mem_span_pow_mul R u π₀ q ℓ (h / (ℓ - 1) + 1) η y hy` to reduce the goal to its premises. Establish `hpos : 0 < ℓ - 1` using `by omega`. Establish `h1 : h < (ℓ - 1) * (h / (ℓ - 1) + 1)` using `Nat.lt_mul_div_succ h hpos`. Establish `h2 : (ℓ - 1) * (h / (ℓ - 1) + 1) ≤ (ℓ - 1) * y` using `Nat.mul_le_mul_left _ hy`.

Use linear arithmetic over natural numbers and integers.
-/
theorem relation_vanishes : RelZero := by
  intro R _ u π₀ q ℓ h η y hℓ hη hy
  apply Formalism.TruncatedSeriesCounting.R9.pow_mem_span_pow_mul R u π₀ q ℓ (h / (ℓ - 1) + 1) η y hy
  have hpos : 0 < ℓ - 1 := by omega
  have h1 : h < (ℓ - 1) * (h / (ℓ - 1) + 1) := Nat.lt_mul_div_succ h hpos
  have h2 : (ℓ - 1) * (h / (ℓ - 1) + 1) ≤ (ℓ - 1) * y := Nat.mul_le_mul_left _ hy
  omega

end Formalism.KernelCokernelLengths
