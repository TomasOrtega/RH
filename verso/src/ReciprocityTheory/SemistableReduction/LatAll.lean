import ReciprocityTheory.SemistableReduction.LemmaH
import ReciprocityTheory.SemistableReduction.BalancedSchwarz
import ReciprocityTheory.SemistableReduction.TorsionNonvanish
import ReciprocityTheory.SemistableReduction.ApproxGraph
import ReciprocityTheory.SemistableReduction.ApproxBasis
import ReciprocityTheory.SemistableReduction.Unipotent
import ReciprocityTheory.SemistableReduction.DegAddHolds
import ReciprocityTheory.SemistableReduction.OnePolyGrowth
import ReciprocityTheory.SemistableReduction.BWPoly
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaH : LemmaHStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.lemmaH_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem balancedSchwarz : BalancedSchwarzStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.balancedSchwarz_holds

/- English proof (translation)
Treat this case separately. Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem torsionNonvanish : TorsionNonvanishStatement := by
  first
    | exact ReciprocityTheory.MultiplicativeHeights.torsionNonvanish_holds
    | exact ReciprocityTheory.MultiplicativeHeights.torsionNonvanish_holds ReciprocityTheory.MultiplicativeHeights.lemmaH_holds
    | exact ReciprocityTheory.MultiplicativeHeights.torsionNonvanish_holds ReciprocityTheory.MultiplicativeHeights.balancedSchwarz_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem approxGraph : ApproxGraphStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.approxGraph_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem approx : ApproxStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.approxBasis_holds ReciprocityTheory.MultiplicativeHeights.approxGraph_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unipotent : UnipotentStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.unipotent_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem degAdd : DegAddStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.degAdd_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem onePolyGrowth : OnePolyGrowthStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.onePolyGrowth_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bwPoly : BWPolyStatement := by
  exact ReciprocityTheory.MultiplicativeHeights.bwPoly_holds ReciprocityTheory.MultiplicativeHeights.lemmaH_holds ReciprocityTheory.L2DbarEstimates.ext
    ReciprocityTheory.MultiplicativeHeights.onePolyGrowth_holds

end ReciprocityTheory.MultiplicativeHeights.Closed
