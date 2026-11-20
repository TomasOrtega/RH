import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
open IsLocalRing Matrix UpperTheory.V.Hi

/- English proof (translation)
Introduce `G _ I A M _ _ _ π a ha v _`. Establish `hfin : ((I.Nconj a).subgroupOf I.N).FiniteIndex` using `⟨I.fin_N a ha⟩`. Use `haveI : Fintype (I.N ⧸ (I.Nconj a).subgroupOf I.N) := Fintype.ofFinite _`. Establish `hc : (I.Nconj a).relIndex I.N = Fintype.card (I.N ⧸ (I.Nconj a).subgroupOf I.N)`. Rewrite using `[← Nat.card_eq_fintype_card]`.

Both sides reduce to the same expression. Establish `hs : (((I.Nconj a).relIndex I.N : ℕ) : A) • π a v = ∑ _q : I.N ⧸ (I.Nconj a).subgroupOf I.N, π a v`. Rewrite using `[Finset.sum_const, Finset.card_univ, hc, Nat.cast_smul_eq_nsmul]`. Rewrite using `[hs, Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun q _ => Submodule.subset_span ?_` and prove the remaining obligations.

Use `⟨(q.out : I.N), I.N_le (q.out).2, π a v, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Hi.propCp :
    ∀ (G : Type) [Group G] (I : Iwa G) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (π : Representation A G M) (a : G), a ∈ I.P → ∀ v ∈ fixd π I.N, I.uOp π a v - ((I.Nconj a).relIndex I.N : A) • π a v ∈ I.jacKer π := by
  intro G _ I A M _ _ _ π a ha v _
  have hfin : ((I.Nconj a).subgroupOf I.N).FiniteIndex := ⟨I.fin_N a ha⟩
  haveI : Fintype (I.N ⧸ (I.Nconj a).subgroupOf I.N) := Fintype.ofFinite _
  have hc : (I.Nconj a).relIndex I.N = Fintype.card (I.N ⧸ (I.Nconj a).subgroupOf I.N) := by
    rw [← Nat.card_eq_fintype_card]; rfl
  have hs : (((I.Nconj a).relIndex I.N : ℕ) : A) • π a v
      = ∑ _q : I.N ⧸ (I.Nconj a).subgroupOf I.N, π a v := by
    rw [Finset.sum_const, Finset.card_univ, hc, Nat.cast_smul_eq_nsmul]
  rw [hs, Iwa.uOp, finsum_eq_sum_of_fintype, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun q _ => Submodule.subset_span ?_
  refine ⟨(q.out : I.N), I.N_le (q.out).2, π a v, ?_⟩
  rw [map_mul]; rfl
