import Formalism.ThetaLogCoordinates.ProductIdealMonotone.ParamDefs

noncomputable section

open scoped BigOperators Classical

namespace Formalism.InvariantFactorPaths.G0

variable {n : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem gam_le {p : ℝ} (hp : 5 ≤ p) : gam p ≤ 25 / (24 * p) := by
  unfold gam
  have h1 : 0 < p ^ 2 - 1 := by nlinarith
  have h2 : 0 < 24 * p := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

end Formalism.InvariantFactorPaths.G0
