import Mathlib
import Formalism.PeriodIntegrals.FoldUnfold
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnfoldingIdentity.FoldUnfoldMain

/- English proof (translation)
The claim follows from `PI.FoldUnfold.UnitaryGroupMassFormula.foldUnfold_main`.
-/
theorem lintegralTransversalSum : PI.FoldUnfold.FoldUnfold :=
  PI.FoldUnfold.UnitaryGroupMassFormula.foldUnfold_main
