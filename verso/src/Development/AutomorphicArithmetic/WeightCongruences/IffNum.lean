import Mathlib
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

namespace UpperTheory.MUQ

variable {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {φ : ι → E →+* K} {e : ι → ℚ}

/- English proof (translation)
Take `⟨a, ha, hMU⟩` from `h`. Establish `: (fun i => (e i).num) = a`. Use function extensionality and compare the values at `i`. Rewrite using `[ha i, Rat.num_intCast]`. Rewrite using `[this]`.

Conclude with `hMU`.
-/
theorem num (h : MUQ φ e) : MU φ (fun i => (e i).num) := by
  obtain ⟨a, ha, hMU⟩ := h
  have : (fun i => (e i).num) = a := by
    funext i
    rw [ha i, Rat.num_intCast]
  rw [this]
  exact hMU

end UpperTheory.MUQ
