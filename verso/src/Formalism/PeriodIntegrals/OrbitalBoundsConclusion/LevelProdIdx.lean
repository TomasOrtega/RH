import Mathlib
import Formalism.PeriodIntegrals.LevelProdIdx
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.ZeroMemLatSet
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.PrVTmulEqTmulApply
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.PrVMemTensInt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelProductIndex.SingleApply

/- English proof (translation)
The claim follows from `PI.LPI.levelProdIdx_of PI.LPI.plDown (PI.LPI.plUp_of PI.LPI.plGen PI.LPI.plInj) (PI.LPI.plLocal_of PI.LPI.plGen PI.LPI.plDown)`.
-/
theorem level_product_index : PI.LevelProdIdx :=
  PI.LPI.levelProdIdx_of PI.LPI.plDown (PI.LPI.plUp_of PI.LPI.plGen PI.LPI.plInj)
    (PI.LPI.plLocal_of PI.LPI.plGen PI.LPI.plDown)
