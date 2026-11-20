import Mathlib
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
import GroundTheory.ProfiniteCohomology.Shapiro
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/- English proof (translation)
Introduce `f`. Establish `hfin : (Set.range (f.1 : G → B)).Finite` using `(isLocallyConstant_coind U B f).range_finite`. Set `N` to `∏ v ∈ hfin.toFinset, addOrderOf v`. Establish `hN : 0 < N` using `Finset.prod_pos fun v _ => (hB v).addOrderOf_pos`. Use `isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, hN, Subtype.ext (funext fun x => ?_)⟩` and prove the remaining obligations.

Use `show N • f.1 x = 0`. Establish `hv : f.1 x ∈ hfin.toFinset` using `by simp`. Conclude with `addOrderOf_dvd_iff_nsmul_eq_zero.1 (Finset.dvd_prod_of_mem _ hv)`.
-/
theorem isAddTorsion_coind (U : OpenSubgroup G) (B : Rep.{u} (ULift.{u} ℤ) (U : Subgroup G))
    [IsDiscreteRep B] (hB : IsAddTorsion B) :
    IsAddTorsion (Rep.coind (U : Subgroup G).subtype B) := by
  classical
  intro f
  have hfin : (Set.range (f.1 : G → B)).Finite := (isLocallyConstant_coind U B f).range_finite
  let N := ∏ v ∈ hfin.toFinset, addOrderOf v
  have hN : 0 < N := Finset.prod_pos fun v _ => (hB v).addOrderOf_pos
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨N, hN, Subtype.ext (funext fun x => ?_)⟩
  show N • f.1 x = 0
  have hv : f.1 x ∈ hfin.toFinset := by simp
  exact addOrderOf_dvd_iff_nsmul_eq_zero.1 (Finset.dvd_prod_of_mem _ hv)

/- English proof (translation)
Rewrite using `[cdp_le_iff]`. Introduce `B _ hB q hq`. Establish `h0` using `primaryComponent_cohomology_eq_bot_of_cdp_lt (Rep.coind (U : Subgroup G).subtype B) (isAddTorsion_coind U B hB) hq`. Rewrite `h0`, the goal using `[primaryComponent_eq_bot_iff]`. Introduce and unpack `x ⟨k, hk⟩`.

Establish `hy : (shapiroIso U B q).inv.hom x = 0` using `h0 _ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩`. Rewrite using `[← Iso.inv_hom_id_apply (shapiroIso U B q) x, hy, map_zero]`.
-/
theorem cdp_openSubgroup_le (p : ℕ) (U : OpenSubgroup G) : cdp p (U : Subgroup G) ≤ cdp p G := by
  rw [cdp_le_iff]
  intro B _ hB q hq
  have h0 := primaryComponent_cohomology_eq_bot_of_cdp_lt (Rep.coind (U : Subgroup G).subtype B)
    (isAddTorsion_coind U B hB) hq
  rw [primaryComponent_eq_bot_iff] at h0 ⊢
  rintro x ⟨k, hk⟩
  have hy : (shapiroIso U B q).inv.hom x = 0 := h0 _ ⟨k, by rw [← map_nsmul, hk, map_zero]⟩
  rw [← Iso.inv_hom_id_apply (shapiroIso U B q) x, hy, map_zero]

end GroundTheory.ProfCoh
