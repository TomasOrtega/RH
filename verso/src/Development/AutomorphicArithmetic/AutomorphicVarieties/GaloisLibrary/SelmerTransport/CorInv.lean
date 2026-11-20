import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCorestrictionCocycle

open ReciprocityTheory.Gal UpperTheory.V.Base

/- English proof (translation)
Introduce `R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U _ h hopen x hx`. Distinguish the cases in `hfin : U'.relIndex U = 0`. Rewrite using `[hfin, zero_smul]`. Conclude with `zero_mem _`. Use `haveI : (U'.subgroupOf U).FiniteIndex := ⟨hfin⟩`.

Use `haveI : Fintype (U ⧸ U'.subgroupOf U) := Fintype.ofFinite _`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `hinv : ∀ g : U, conjU ρ U' g (Submodule.Quotient.mk z) = Submodule.Quotient.mk z` using `fun g => (Representation.mem_invariants _ _).mp hx g`. Establish `hq : ∀ q : U ⧸ U'.subgroupOf U, ∃ m : M, ∀ u : U', ρ (q.out : G) (z.1 (conjHom U' (q.out : G) u)) - z.1 u = ρ u m - m`. Introduce `q`.

Take `⟨z', hz1, hz2⟩` from `conjU_mk ρ U' (q.out : G) z`. Rewrite `hz1` using `[hinv, mk_eq_mk]`. Take `⟨m, hm⟩` from `hz1`. Use `⟨-m, fun u => ?_⟩` and prove the remaining obligations. Establish `e` using `hm u`.

Rewrite `e` using `[hz2]`. Rewrite using `[map_neg, neg_sub_neg, ← neg_sub ((ρ u) m) m, ← e]`. Normalize the expressions using the abelian group laws. Use `choose mq hmq using hq`. Set `f : U → M` to `fun g => if hg : (g : G) ∈ U' then z.1 ⟨g, hg⟩ else 0`.

Establish `hfc : ContinuousOn f (U'.subgroupOf U : Set U)`. Rewrite using `[continuousOn_iff_continuous_restrict]`. Use `(z.2.1.comp (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) (fun g : (U'.subgroupOf U : Set U) => Subgroup.mem_subgroupOf.mp g.2))).congr ?_` and prove the remaining obligations. Introduce `g`. Simplify using `[f, dif_pos (Subgroup.mem_subgroupOf.mp g.2)]`.

Establish `hfcoc : ∀ g ∈ U'.subgroupOf U, ∀ k ∈ U'.subgroupOf U, f (g * k) = f g + (ρ.comp U.subtype) g (f k)`. Introduce `g hg k hk`. Rewrite `hg`, `hk` using `[Subgroup.mem_subgroupOf]`. Establish `hgk : ((g * k : U) : G) ∈ U'`. Rewrite using `[Subgroup.coe_mul]`.

Conclude with `U'.mul_mem hg hk`. Simplify using `only [f, dif_pos hg, dif_pos hk, dif_pos hgk]`. Conclude with `z.2.2 ⟨g, hg⟩ ⟨k, hk⟩`. Take `⟨F, hFc, hFcoc, ⟨x0, hx0⟩, -⟩` from `GlobalTheory.exists_corestriction_cocycle R U M (ρ.comp U.subtype) (U'.subgroupOf U) hopen (fun _ => continuous_of_discreteTopology) (fun m => hρ.comp (Continuous.prodMk (continuous_subtype_val) continuous_const)) f hfc hfcoc`. Set `Fz : Z1U ρ U` to `⟨F, hFc, hFcoc⟩`.

Use `⟨Submodule.Quotient.mk Fz, ?_⟩` and prove the remaining obligations. Take `⟨w, hw1, hw2⟩` from `resU_mk ρ h Fz`. Rewrite using `[hw1, ← Submodule.Quotient.mk_smul, mk_eq_mk]`. Use `⟨x0 + ∑ q, mq q, fun u => ?_⟩` and prove the remaining obligations. Establish `hterm : ∀ q : U ⧸ U'.subgroupOf U, (ρ.comp U.subtype) q.out (f ((q.out)⁻¹ * ⟨(u : G), h u.2⟩ * q.out)) = z.1 u + (ρ u (mq q) - mq q)`.

Introduce `q`. Rewrite using `[← hmq q u, add_sub_cancel]`. Establish `hmem : (((q.out)⁻¹ * ⟨(u : G), h u.2⟩ * q.out : U) : G) ∈ U'`. Establish `e` using `‹U'.Normal›.conj_mem u u.2 ((q.out : G)⁻¹)`. Simplify `e` using `[mul_assoc]`.

Simplify using `only [f, dif_pos hmem]`. Both sides reduce to the same expression. Establish `hcard : Fintype.card (U ⧸ U'.subgroupOf U) = U'.relIndex U`. Rewrite using `[Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]`. Rewrite using `[hw2 u]`.

Use `show F ⟨(u : G), h u.2⟩ - _ = _`. Rewrite using `[hx0 ⟨u, h u.2⟩ (Subgroup.mem_subgroupOf.mpr u.2), finsum_eq_sum_of_fintype, Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, hcard]`. Simplify using `only [Submodule.coe_smul, Pi.smul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, map_add, map_sum]`. Rewrite using `[show ((U'.relIndex U • z : Z1U ρ U') : U' → M) u = U'.relIndex U • z.1 u from rfl]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.V.Base.corInv :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsOpen (U'.subgroupOf U : Set U) →
      ∀ x ∈ invariantsUnderSubgroupH1 ρ U U', U'.relIndex U • x ∈ LinearMap.range (resU ρ h) := by
  classical
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U _ h hopen x hx
  by_cases hfin : U'.relIndex U = 0
  · rw [hfin, zero_smul]
    exact zero_mem _
  haveI : (U'.subgroupOf U).FiniteIndex := ⟨hfin⟩
  haveI : Fintype (U ⧸ U'.subgroupOf U) := Fintype.ofFinite _
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hinv : ∀ g : U, conjU ρ U' g (Submodule.Quotient.mk z) = Submodule.Quotient.mk z :=
    fun g => (Representation.mem_invariants _ _).mp hx g
  have hq : ∀ q : U ⧸ U'.subgroupOf U, ∃ m : M, ∀ u : U',
      ρ (q.out : G) (z.1 (conjHom U' (q.out : G) u)) - z.1 u = ρ u m - m := by
    intro q
    obtain ⟨z', hz1, hz2⟩ := conjU_mk ρ U' (q.out : G) z
    rw [hinv, mk_eq_mk] at hz1
    obtain ⟨m, hm⟩ := hz1
    refine ⟨-m, fun u => ?_⟩
    have e := hm u
    rw [hz2] at e
    rw [map_neg, neg_sub_neg, ← neg_sub ((ρ u) m) m, ← e]
    abel
  choose mq hmq using hq
  let f : U → M := fun g => if hg : (g : G) ∈ U' then z.1 ⟨g, hg⟩ else 0
  have hfc : ContinuousOn f (U'.subgroupOf U : Set U) := by
    rw [continuousOn_iff_continuous_restrict]
    refine (z.2.1.comp (Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun g : (U'.subgroupOf U : Set U) => Subgroup.mem_subgroupOf.mp g.2))).congr ?_
    intro g
    simp [f, dif_pos (Subgroup.mem_subgroupOf.mp g.2)]
  have hfcoc : ∀ g ∈ U'.subgroupOf U, ∀ k ∈ U'.subgroupOf U,
      f (g * k) = f g + (ρ.comp U.subtype) g (f k) := by
    intro g hg k hk
    rw [Subgroup.mem_subgroupOf] at hg hk
    have hgk : ((g * k : U) : G) ∈ U' := by
      rw [Subgroup.coe_mul]
      exact U'.mul_mem hg hk
    simp only [f, dif_pos hg, dif_pos hk, dif_pos hgk]
    exact z.2.2 ⟨g, hg⟩ ⟨k, hk⟩
  obtain ⟨F, hFc, hFcoc, ⟨x0, hx0⟩, -⟩ := GlobalTheory.exists_corestriction_cocycle R U M
    (ρ.comp U.subtype) (U'.subgroupOf U) hopen (fun _ => continuous_of_discreteTopology)
    (fun m => hρ.comp (Continuous.prodMk
      (continuous_subtype_val) continuous_const)) f hfc hfcoc
  let Fz : Z1U ρ U := ⟨F, hFc, hFcoc⟩
  refine ⟨Submodule.Quotient.mk Fz, ?_⟩
  obtain ⟨w, hw1, hw2⟩ := resU_mk ρ h Fz
  rw [hw1, ← Submodule.Quotient.mk_smul, mk_eq_mk]
  refine ⟨x0 + ∑ q, mq q, fun u => ?_⟩
  have hterm : ∀ q : U ⧸ U'.subgroupOf U,
      (ρ.comp U.subtype) q.out (f ((q.out)⁻¹ * ⟨(u : G), h u.2⟩ * q.out)) =
        z.1 u + (ρ u (mq q) - mq q) := by
    intro q
    rw [← hmq q u, add_sub_cancel]
    have hmem : (((q.out)⁻¹ * ⟨(u : G), h u.2⟩ * q.out : U) : G) ∈ U' := by
      have e := ‹U'.Normal›.conj_mem u u.2 ((q.out : G)⁻¹)
      simpa [mul_assoc] using e
    simp only [f, dif_pos hmem]
    rfl
  have hcard : Fintype.card (U ⧸ U'.subgroupOf U) = U'.relIndex U := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [hw2 u]
  show F ⟨(u : G), h u.2⟩ - _ = _
  rw [hx0 ⟨u, h u.2⟩ (Subgroup.mem_subgroupOf.mpr u.2), finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, hcard]
  simp only [Submodule.coe_smul, Pi.smul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    map_add, map_sum]
  rw [show ((U'.relIndex U • z : Z1U ρ U') : U' → M) u = U'.relIndex U • z.1 u from rfl]
  abel
