import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.ConverseStepOf

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stabPairs : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree :=
  PI.StabPairsW.stabPairs_of_converse (PI.StabPairs.Conv.converseStep_of PI.StabPairsW.gram_matrix_invariance)
