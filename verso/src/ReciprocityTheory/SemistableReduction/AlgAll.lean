import ReciprocityTheory.SemistableReduction.FinrankRestrictTotalDegree
import ReciprocityTheory.SemistableReduction.RankEqualityHolds
import ReciprocityTheory.SemistableReduction.CauchyInequalityOnTorus
import ReciprocityTheory.SemistableReduction.GenericImageFinite
import ReciprocityTheory.SemistableReduction.IntegralClosureRankAndResidueTrdegLe
import ReciprocityTheory.SemistableReduction.GaussExtensionAndResidueTrdegEq
import Mathlib
import ReciprocityTheory.SemistableReduction.DetSubtypeCompAssociatedProd
import ReciprocityTheory.SemistableReduction.NormValuationEqFactorization

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

/- English proof (translation)
The claim follows from `rank_equality_holds`.
-/
theorem rank : RankStatement := rank_equality_holds

/- English proof (translation)
The claim follows from `genericImageFinite`.
-/
theorem fieldOfS : FieldOfSStatement := genericImageFinite

/- English proof (translation)
The claim follows from `integralClosureRank_and_residueTrdegLe.1`.
-/
theorem dedekindRank : DedekindRankStatement := integralClosureRank_and_residueTrdegLe.1

/- English proof (translation)
The claim follows from `residueTrdegLe`.
-/
theorem tr : TRStatement := residueTrdegLe

/- English proof (translation)
The claim follows from `residueTrdeg_holds residueTrdegLe`.
-/
theorem residueTrdeg : ResidueTrdegStatement := residueTrdeg_holds residueTrdegLe

/- English proof (translation)
The claim follows from `gaugeSplitting_holds`.
-/
theorem normLength : NormLengthStatement := gaugeSplitting_holds

/- English proof (translation)
The claim follows from `normValuation_eq_factorization normLength`.
-/
theorem normOrd : NormOrdStatement := normValuation_eq_factorization normLength

end ReciprocityTheory.MultiplicativeHeights.Closed
