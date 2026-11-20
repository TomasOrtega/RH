import Formalism.PadicSubsetSums.CentralIdempotents.GL2UnipotentBruhatDecomposition
import Formalism.PadicSubsetSums.StableGradedCounts.FrobeniusDifferenceDividedPower
import Formalism.PadicSubsetSums.StableGradedCounts.LiftingTheExponent
import Formalism.PadicSubsetSums.StableGradedCounts.TWCentralIdempotentIntegral
import Formalism.PadicSubsetSums.StableGradedCounts.PadicValCardGL

namespace Formalism.IrreducibleCountingLemmas.WindowSums

open Polynomial TensorProduct

/- English proof (translation)
Establish `h1 : (l : ℝ) ^ (Nat.log l n) ≤ n` using `by exact_mod_cast Nat.pow_log_le_self l (by omega)`. Establish `hl' : (1 : ℝ) < l` using `by exact_mod_cast hl`. Rewrite using `[Real.le_logb_iff_rpow_le hl' (by exact_mod_cast hn), Real.rpow_natCast]`. Conclude with `h1`.
-/
theorem natLog_le_logb (l n : ℕ) (hl : 2 ≤ l) (hn : 1 ≤ n) : (Nat.log l n : ℝ) ≤ Real.logb l n := by
  have h1 : (l : ℝ) ^ (Nat.log l n) ≤ n := by exact_mod_cast Nat.pow_log_le_self l (by omega)
  have hl' : (1 : ℝ) < l := by exact_mod_cast hl
  rw [Real.le_logb_iff_rpow_le hl' (by exact_mod_cast hn), Real.rpow_natCast]
  exact h1

section Frame

open scoped Matrix

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

end Frame

end Formalism.IrreducibleCountingLemmas.WindowSums
