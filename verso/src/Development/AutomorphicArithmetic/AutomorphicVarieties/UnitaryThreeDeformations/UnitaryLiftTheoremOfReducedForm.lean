import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostNumber
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IrrCyc
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPtOfIsPtHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.HostOk
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia

/- English proof (translation)
Rewrite using `[totallyDisconnectedSpace_iff_connectedComponent_one]`. Use `Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨x, rfl⟩` from `QuotientGroup.mk_surjective y`. Assume the negation of the conclusion as `hx`. Establish `hx' : x ∉ N` using `fun h => hx ((QuotientGroup.eq_one_iff x).2 h)`.

Establish `ho : IsOpen {g : G | g * x ∉ N}` using `hN.isOpen_compl.preimage (continuous_mul_const x)`. Take `⟨U, hU⟩` from `ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')`. Set `V : Subgroup (G ⧸ N)` to `U.toSubgroup.map (QuotientGroup.mk' N)`. Establish `hVo : IsOpen (V : Set (G ⧸ N))` using `QuotientGroup.isOpenMap_coe _ U.isOpen'`. Establish `hV : IsClopen (V : Set (G ⧸ N))` using `⟨V.isClosed_of_isOpen hVo, hVo⟩`.

Take `⟨u, hu, hux⟩` from `hV.connectedComponent_subset V.one_mem hy`. Conclude with `hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)`.
-/
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
