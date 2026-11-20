import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

/- English proof (translation)
Introduce `G H _ _ ι Γ U K hΓ hU ⟨T, hT⟩`. Use `haveI : Fintype (H ⧸ Γ) := Subgroup.fintypeOfIndexNeZero hΓ.index_ne_zero`. Use `haveI : Fintype (K ⧸ U.subgroupOf K) := Subgroup.fintypeOfIndexNeZero hU`. Use `⟨((Finset.univ : Finset (H ⧸ Γ)) ×ˢ T ×ˢ (Finset.univ : Finset (K ⧸ U.subgroupOf K))).image (fun x => ι (x.1.out)⁻¹ * x.2.1 * ((x.2.2.out : K) : G)), fun g => ?_⟩` and prove the remaining obligations. Take `⟨h, t, ht, k, hk, rfl⟩` from `hT g`.

Take `⟨γ, hγ⟩` from `QuotientGroup.mk_out_eq_mul Γ h⁻¹`. Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul (U.subgroupOf K) (⟨k, hk⟩ : K)`. Establish `huU : (((u : K) : G))⁻¹ ∈ U` using `U.inv_mem (Subgroup.mem_subgroupOf.1 u.2)`. Use `⟨γ, γ.2, _, Finset.mem_image.2 ⟨(QuotientGroup.mk h⁻¹, t, QuotientGroup.mk ⟨k, hk⟩), ?_, rfl⟩, _, huU, ?_⟩` and prove the remaining obligations. Simplify using `[ht]`.

Simplify using `only [hγ, hu, mul_inv_rev, inv_inv, map_mul, map_inv, Subgroup.coe_mul] group`.
-/
theorem UpperTheory.adelic_cohomology_finite_orbit_bound :
    UpperTheory.V.Af.CohB.FinOrbAbs := by
  classical
  intro G H _ _ ι Γ U K hΓ hU ⟨T, hT⟩
  haveI : Fintype (H ⧸ Γ) := Subgroup.fintypeOfIndexNeZero hΓ.index_ne_zero
  haveI : Fintype (K ⧸ U.subgroupOf K) := Subgroup.fintypeOfIndexNeZero hU
  refine ⟨((Finset.univ : Finset (H ⧸ Γ)) ×ˢ T ×ˢ (Finset.univ : Finset (K ⧸ U.subgroupOf K))).image
    (fun x => ι (x.1.out)⁻¹ * x.2.1 * ((x.2.2.out : K) : G)), fun g => ?_⟩
  obtain ⟨h, t, ht, k, hk, rfl⟩ := hT g
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul Γ h⁻¹
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf K) (⟨k, hk⟩ : K)
  have huU : (((u : K) : G))⁻¹ ∈ U := U.inv_mem (Subgroup.mem_subgroupOf.1 u.2)
  refine ⟨γ, γ.2, _, Finset.mem_image.2 ⟨(QuotientGroup.mk h⁻¹, t, QuotientGroup.mk ⟨k, hk⟩), ?_, rfl⟩,
    _, huU, ?_⟩
  · simp [ht]
  · simp only [hγ, hu, mul_inv_rev, inv_inv, map_mul, map_inv, Subgroup.coe_mul]
    group
