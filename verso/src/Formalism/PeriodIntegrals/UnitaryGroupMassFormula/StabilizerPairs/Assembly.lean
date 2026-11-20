import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.StabPairsOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.Forward
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd

namespace PI.StabPairsW

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gram_matrix_invariance : GramInv := gramInv_of frameInd

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stabilizer_pair_formula : PairFormula := pairFormula_of gram_matrix_invariance

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem stabPairs_of_converse (h : ConverseStep) : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree :=
  stabPairs_of mapsStep stabilizer_pair_formula h compDet

end PI.StabPairsW
