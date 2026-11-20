import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.IdemDen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.IdempotentEvaluation.IdemEval
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.IdempotentEvaluation.DualDiff

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.TBIdemDen.idemEval`.
-/
theorem idempotent_evaluation : ReciprocityTheory.ChartRestriction.G.TB.IdemEvalSt := PI.UnitaryGroupMassFormula.TBIdemDen.idemEval
/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.TBIdemDen.dualDiff`.
-/
theorem dual_difference : ReciprocityTheory.ChartRestriction.G.TB.DualDiffSt := PI.UnitaryGroupMassFormula.TBIdemDen.dualDiff
