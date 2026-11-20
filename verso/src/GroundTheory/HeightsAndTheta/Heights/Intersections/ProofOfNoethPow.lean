import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerTail
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisBis
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsUnitOfNumMem
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingFrac
import GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingLocal
import GroundTheory.HeightsAndTheta.Heights.Intersections.SpanSingletonEqRangeLsmul
import GroundTheory.HeightsAndTheta.Heights.Intersections.CardLength
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.KrullDimQuotientEqOneIffEqBot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

/- English proof (translation)
Introduce `K _ ι _ P s a W y hP hs hsP hW hy hy0`. Take `⟨hloc, hnoeth, hdim⟩` from `hD K ι P s a W hP hs hsP hW`. Use `hloc` as an intermediate fact. Use `hnoeth` as an intermediate fact. Establish `: P.IsPrime` using `hP.2.1.1`.

Establish `: IsDomain (locRing P W)` using `inferInstance`. Establish `: Ring.KrullDimLE 1 (locRing P W)` using `ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hdim`. Take `⟨hfinRes, -⟩` from `regularityLocalResidue_holds.proof K ι P s a W (fun i => i.elim0) hP hs hsP hW`. Establish `hy0' : (⟨y, hy⟩ : locRing P W) ≠ 0` using `fun h => hy0 (congrArg Subtype.val h)`. Establish `hfin : Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y) ≠ ⊤`.

Rewrite using `[locIdeal_eq_span hy, span_singleton_eq_range_lsmul]`. Conclude with `ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top (locRing P W) hy0'`. Establish `hcard` using `card_eq_card_residueField_pow_length (locRing P W ⧸ locIdeal P W y) hfin`. Establish `hpos : 0 < Nat.card (IsLocalRing.ResidueField (locRing P W))` using `Nat.card_pos`. Apply `Nat.finite_of_card_ne_zero` to reduce the goal to its premises.

Rewrite using `[hcard]`. Conclude with `pow_ne_zero _ hpos.ne'`.
-/
theorem RegularityLocalFinite.proof (hD : regularityLocalDimension_holds.Statement) : RegularityLocalFinite.Statement := by
  intro K _ ι _ P s a W y hP hs hsP hW hy hy0
  obtain ⟨hloc, hnoeth, hdim⟩ := hD K ι P s a W hP hs hsP hW
  have := hloc
  have := hnoeth
  have : P.IsPrime := hP.2.1.1
  have : IsDomain (locRing P W) := inferInstance
  have : Ring.KrullDimLE 1 (locRing P W) := ReciprocityTheory.ChartRestriction.G.AI.krullDimLE_one_of_krullDim_eq hdim
  obtain ⟨hfinRes, -⟩ := regularityLocalResidue_holds.proof K ι P s a W (fun i => i.elim0) hP hs hsP hW
  have hy0' : (⟨y, hy⟩ : locRing P W) ≠ 0 := fun h => hy0 (congrArg Subtype.val h)
  have hfin : Module.length (locRing P W) (locRing P W ⧸ locIdeal P W y) ≠ ⊤ := by
    rw [locIdeal_eq_span hy, span_singleton_eq_range_lsmul]
    exact ReciprocityTheory.ChartRestriction.G.AI.length_coker_ne_top (locRing P W) hy0'
  have hcard := card_eq_card_residueField_pow_length (locRing P W ⧸ locIdeal P W y) hfin
  have hpos : 0 < Nat.card (IsLocalRing.ResidueField (locRing P W)) := Nat.card_pos
  apply Nat.finite_of_card_ne_zero
  rw [hcard]
  exact pow_ne_zero _ hpos.ne'

end

end GroundTheory.Heights₂.Heights.Inter
