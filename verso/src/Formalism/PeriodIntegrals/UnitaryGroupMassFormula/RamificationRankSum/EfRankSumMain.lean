import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.Lattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RamificationRankSum.Points

namespace PI.UnitaryGroupMassFormula.EfRankSum

open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing

/- English proof (translation)
Establish `: Finite (Pts O A)` using `finite_pts O A`. Set `: Fintype (Pts O A)` to `Fintype.ofFinite _`. Set `: Fintype ((maximalIdeal O).primesOver ↥(As O A))` to `Fintype.ofEquiv _ (ptsEquiv O A)`. Rewrite using `[finsum_eq_sum_of_fintype, ← Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal O), ← (ptsEquiv O A).sum_comp]`. Use `Finset.sum_congr rfl fun ζ _ => ?_` and prove the remaining obligations.

Rewrite using `[ptsEquiv_apply, ep_eq_ramificationIdx hϖ, fdeg_eq_inertiaDeg]`.
-/
theorem sum_ef (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O ↥(As O A)] [Module.Flat O ↥(As O A)]
    {ϖ : O} (hϖ : Irreducible ϖ) :
    (∑ᶠ ζ : Pts O A, ep ϖ ζ * fdeg ζ) = Module.finrank O ↥(As O A) := by
  classical
  have : Finite (Pts O A) := finite_pts O A
  let : Fintype (Pts O A) := Fintype.ofFinite _
  let : Fintype ((maximalIdeal O).primesOver ↥(As O A)) := Fintype.ofEquiv _ (ptsEquiv O A)
  rw [finsum_eq_sum_of_fintype, ← Ideal.sum_ramification_inertia_eq_finrank (maximalIdeal O),
    ← (ptsEquiv O A).sum_comp]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  rw [ptsEquiv_apply, ep_eq_ramificationIdx hϖ, fdeg_eq_inertiaDeg]

/- English proof (translation)
Introduce `O _ _ _ K _ _ _ A _ _ _ _ _ _ ϖ hϖ hfin _`. Use `haveI : Module.Free O ↥(As O A) := free_as O K A`. Conclude with `⟨finite_pts O A, by rw [sum_ef O A hϖ, finrank_as O K A]⟩`.
-/
theorem efRankSum_main : PI.EfRankSum := by
  intro O _ _ _ K _ _ _ A _ _ _ _ _ _ ϖ hϖ hfin _
  haveI : Module.Free O ↥(As O A) := free_as O K A
  exact ⟨finite_pts O A, by rw [sum_ef O A hϖ, finrank_as O K A]⟩

end PI.UnitaryGroupMassFormula.EfRankSum
