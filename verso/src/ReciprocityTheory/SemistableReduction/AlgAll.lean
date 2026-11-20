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
A detailed English derivation is pending.
-/
theorem rank : RankStatement := rank_equality_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fieldOfS : FieldOfSStatement := genericImageFinite

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dedekindRank : DedekindRankStatement := integralClosureRank_and_residueTrdegLe.1

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tr : TRStatement := residueTrdegLe

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem residueTrdeg : ResidueTrdegStatement := residueTrdeg_holds residueTrdegLe

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem normLength : NormLengthStatement := gaugeSplitting_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem normOrd : NormOrdStatement := normValuation_eq_factorization normLength

end ReciprocityTheory.MultiplicativeHeights.Closed
