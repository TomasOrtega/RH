import Mathlib
import Formalism.PeriodIntegrals.SelfDualOfDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KernelSplitting.IsIntegralHalf

/- English proof (translation)
Introduce `K E _ _ _ _ _ cj d p s hd hs hcj hp hJ`. Distinguish the cases in `h2 : p = 2`. Substitute `h2` using the available equality. Conclude with `PI.UnitaryGroupMassFormula.KerSplit.splitsAt_two cj d s hd hs hcj`. Conclude with `PI.UnitaryGroupMassFormula.KerSplit.splitsAt_odd cj d p s hs hcj hp h2 (hJ.resolve_left h2)`.
-/
theorem kernel_split_of_jacobi : PI.KerIso.SplitOfJacobi := by
  intro K E _ _ _ _ _ cj d p s hd hs hcj hp hJ
  by_cases h2 : p = 2
  · subst h2
    exact PI.UnitaryGroupMassFormula.KerSplit.splitsAt_two cj d s hd hs hcj
  · exact PI.UnitaryGroupMassFormula.KerSplit.splitsAt_odd cj d p s hs hcj hp h2 (hJ.resolve_left h2)
