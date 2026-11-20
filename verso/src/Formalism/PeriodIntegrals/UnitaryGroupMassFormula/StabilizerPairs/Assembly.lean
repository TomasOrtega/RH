import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.StabPairsOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerPairs.Forward
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FrameInd

namespace PI.StabPairsW

/- English proof (translation)
The claim follows from `gramInv_of frameInd`.
-/
theorem gram_matrix_invariance : GramInv := gramInv_of frameInd

/- English proof (translation)
The claim follows from `pairFormula_of gram_matrix_invariance`.
-/
theorem stabilizer_pair_formula : PairFormula := pairFormula_of gram_matrix_invariance

/- English proof (translation)
The claim follows from `stabPairs_of mapsStep stabilizer_pair_formula h compDet`.
-/
theorem stabPairs_of_converse (h : ConverseStep) : Formalism.FourierDecayAlt.C2.CurvatureConditionOneClauseThree :=
  stabPairs_of mapsStep stabilizer_pair_formula h compDet

end PI.StabPairsW
