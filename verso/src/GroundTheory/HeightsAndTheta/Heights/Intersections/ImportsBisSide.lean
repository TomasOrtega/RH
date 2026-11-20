import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemFunFieldSpecZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerFurther
import GroundTheory.HeightsAndTheta.Heights.Intersections.TwoMemRegRingSpecZ
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreBis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CardQuotEqNatAbsNorm
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ P b hP hb hbW`. Take `⟨hF, hNF⟩` from `hN K ι P hP`. Set `_` to `hF.toField`. Use `hNF` as an intermediate fact. Take `⟨hfree, hfin, hrank⟩` from `hO K ι P hP`.

Set `b' : regRing P` to `⟨b, hbW⟩`. Establish `hb' : b' ≠ 0` using `fun h => hb (congrArg Subtype.val h)`. Take `⟨hfs, hsum⟩` from `hL K ι P b' hP hb'`. Use `⟨hfs, hsum.trans ?_⟩` and prove the remaining obligations. Establish `hI` using `(ReciprocityTheory.ChartRestriction.G.AI.index_thm (funField P) (regRing P) hfree hfin (hrank hF) b' hb').2`.

Conclude with `hI.trans (finsum_eq_sum_of_fintype _).symm`.
-/
theorem RegularityFormula.proof (hN : RegularityFunctionFieldNumber.Statement) (hO : RegularityOrder.Statement)
    (hL : RegularityLocal.Statement) : RegularityFormula.Statement := by
  classical
  intro K _ ι _ P b hP hb hbW
  obtain ⟨hF, hNF⟩ := hN K ι P hP
  let _ := hF.toField
  have := hNF
  obtain ⟨hfree, hfin, hrank⟩ := hO K ι P hP
  let b' : regRing P := ⟨b, hbW⟩
  have hb' : b' ≠ 0 := fun h => hb (congrArg Subtype.val h)
  obtain ⟨hfs, hsum⟩ := hL K ι P b' hP hb'
  refine ⟨hfs, hsum.trans ?_⟩
  have hI := (ReciprocityTheory.ChartRestriction.G.AI.index_thm (funField P) (regRing P) hfree hfin (hrank hF) b' hb').2
  exact hI.trans (finsum_eq_sum_of_fintype _).symm

end

end GroundTheory.Heights₂.Heights.Inter
