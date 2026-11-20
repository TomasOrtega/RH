import Mathlib
import Formalism.PeriodIntegrals.RowLetter
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.ChainRule
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.NvFalseEq

/- English proof (translation)
The claim follows from `PI.RL.W.rowLetter_of PI.RL.W.chainRule PI.RL.W.vecX PI.RL.W.keyCov PI.RL.W.hdHom`.
-/
theorem row_letter_rule : PI.RowLetter :=
  PI.RL.W.rowLetter_of PI.RL.W.chainRule PI.RL.W.vecX PI.RL.W.keyCov PI.RL.W.hdHom
