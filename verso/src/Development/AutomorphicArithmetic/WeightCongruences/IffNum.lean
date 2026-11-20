import Mathlib
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

namespace UpperTheory.MUQ

variable {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {φ : ι → E →+* K} {e : ι → ℚ}

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem num (h : MUQ φ e) : MU φ (fun i => (e i).num) := by
  obtain ⟨a, ha, hMU⟩ := h
  have : (fun i => (e i).num) = a := by
    funext i
    rw [ha i, Rat.num_intCast]
  rw [this]
  exact hMU

end UpperTheory.MUQ
