import Mathlib
import Formalism.PeriodIntegrals.RhsWLim
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.VolumeLieE

noncomputable section

namespace PI.RhsWLim.W

open PI.RhsWLim

/- English proof (translation)
Introduce `k hk`. Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`. Simplify using `only [volU, Finset.prod_range_succ, Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem volURatio : VolURatio := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [volU, Finset.prod_range_succ, Nat.add_sub_cancel]
  ring

end PI.RhsWLim.W
