import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Transg
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DenseGen

open ReciprocityTheory.Gal UpperTheory.V.Base

/- English proof (translation)
Establish `hc : ∀ g m, (LinearMap.id : N →ₗ[R] N) ((σ.comp e.symm.toMonoidHom : Representation R Q' N) (e.toMonoidHom g) m) = σ g ((LinearMap.id : N →ₗ[R] N) m)` using `fun g m => by simp`. Establish `hsurj : Function.Surjective (compatiblePairH2 (σ.comp e.symm.toMonoidHom : Representation R Q' N) σ e.toMonoidHom he LinearMap.id continuous_id hc)`. Introduce `x`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Use `⟨Submodule.Quotient.mk (restrictCocycles2 σ e.symm.toMonoidHom he' z), ?_⟩` and prove the remaining obligations.

Use `show Submodule.Quotient.mk (compatiblePairCocycles2 _ σ e.toMonoidHom he LinearMap.id continuous_id hc _) = _`. Use `congr 1`. Use `Subtype.ext (funext fun p => ?_)` and prove the remaining obligations. Take `⟨g, h⟩` from `p`. Use `show z.1 (e.symm (e g), e.symm (e h)) = _`.

Simplify using the standard rewrite rules. Conclude with `hsurj.subsingleton`.
-/
private theorem H2_subsingleton_of_mulEquiv {R Q Q' N : Type} [CommRing R] [Group Q] [TopologicalSpace Q] [Group Q'] [TopologicalSpace Q']
    [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousConstSMul R N]
    (σ : Representation R Q N) (e : Q ≃* Q') (he : Continuous e) (he' : Continuous e.symm)
    (hs : Subsingleton (H2 (σ.comp e.symm.toMonoidHom : Representation R Q' N))) : Subsingleton (H2 σ) := by
  have hc : ∀ g m, (LinearMap.id : N →ₗ[R] N) ((σ.comp e.symm.toMonoidHom : Representation R Q' N) (e.toMonoidHom g) m)
      = σ g ((LinearMap.id : N →ₗ[R] N) m) := fun g m => by simp
  have hsurj : Function.Surjective
      (compatiblePairH2 (σ.comp e.symm.toMonoidHom : Representation R Q' N) σ e.toMonoidHom he LinearMap.id continuous_id hc) := by
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨Submodule.Quotient.mk (restrictCocycles2 σ e.symm.toMonoidHom he' z), ?_⟩
    show Submodule.Quotient.mk (compatiblePairCocycles2 _ σ e.toMonoidHom he LinearMap.id continuous_id hc _) = _
    congr 1
    refine Subtype.ext (funext fun p => ?_)
    obtain ⟨g, h⟩ := p
    show z.1 (e.symm (e g), e.symm (e h)) = _
    simp
  exact hsurj.subsingleton

/- English proof (translation)
Unfold `ReciprocityTheory.Gal.ContAction`. Establish `hq` using `(QuotientGroup.isOpenQuotientMap_mk (N := S)).prodMap (IsOpenQuotientMap.id (X := Representation.invariants (ρ.comp S.subtype)))`. Rewrite using `[← hq.continuous_comp_iff]`. Use `Continuous.subtype_mk (f := fun p : G × Representation.invariants (ρ.comp S.subtype) => ρ p.1 p.2.1) ?_ _` and prove the remaining obligations. Conclude with `hρ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))`.
-/
private theorem cont_quot {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    (ρ : Representation R G M) (hρ : ReciprocityTheory.Gal.ContAction ρ) (S : Subgroup G) [S.Normal] :
    ReciprocityTheory.Gal.ContAction (ρ.quotientToInvariants S) := by
  unfold ReciprocityTheory.Gal.ContAction
  have hq := (QuotientGroup.isOpenQuotientMap_mk (N := S)).prodMap
    (IsOpenQuotientMap.id (X := Representation.invariants (ρ.comp S.subtype)))
  rw [← hq.continuous_comp_iff]
  refine Continuous.subtype_mk (f := fun p : G × Representation.invariants (ρ.comp S.subtype) => ρ p.1 p.2.1) ?_ _
  exact hρ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/- English proof (translation)
Set `e : G ⧸ S ≃* Multiplicative ℤ_[l]` to `(QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective κ hs)`. Establish `he : Continuous e`. Rewrite using `[← (QuotientGroup.isOpenQuotientMap_mk (N := S)).continuous_comp_iff]`. Conclude with `hκ`. Establish `he' : Continuous e.symm` using `(Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) he).symm.continuous`.

Use `H2_subsingleton_of_mulEquiv _ e he he' (h2Zl l R _ _ ?_ ?_)` and prove the remaining obligations. Conclude with `(cont_quot ρ hρ S).comp ((he'.comp continuous_fst).prodMk continuous_snd)`. Introduce `m`. Take `⟨n, hn⟩` from `hl m.1`. Conclude with `⟨n, Subtype.ext (by simpa using hn)⟩`.
-/
private theorem H2_quotientToInvariants_subsingleton_of_zl_quotient (l : ℕ) [Fact l.Prime] {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [ContinuousConstSMul R M] [DiscreteTopology M]
    (ρ : Representation R G M) (hρ : ReciprocityTheory.Gal.ContAction ρ) (hl : ∀ m : M, ∃ n : ℕ, l ^ n • m = 0) (S : Subgroup G) [S.Normal]
    (κ : G →* Multiplicative ℤ_[l]) (hκ : Continuous κ) (hs : Function.Surjective κ) (hk : κ.ker = S) :
    Subsingleton (H2 (ρ.quotientToInvariants S)) := by
  let e : G ⧸ S ≃* Multiplicative ℤ_[l] :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivOfSurjective κ hs)
  have he : Continuous e := by
    rw [← (QuotientGroup.isOpenQuotientMap_mk (N := S)).continuous_comp_iff]
    exact hκ
  have he' : Continuous e.symm := (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv) he).symm.continuous
  refine H2_subsingleton_of_mulEquiv _ e he he' (h2Zl l R _ _ ?_ ?_)
  · exact (cont_quot ρ hρ S).comp ((he'.comp continuous_fst).prodMk continuous_snd)
  · intro m
    obtain ⟨n, hn⟩ := hl m.1
    exact ⟨n, Subtype.ext (by simpa using hn)⟩

/- English proof (translation)
Introduce `l _ R G M _ _ _ _ _ _ _ _ _ _ ρ _ _ _ hρ hl U' U _ h hU κ hκ hs hk`. Use `haveI : CompactSpace U := isCompact_iff_compactSpace.1 hU.isCompact`. Establish `hρU : ReciprocityTheory.Gal.ContAction (ρ.comp U.subtype : Representation R U M)` using `hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)`. Use `haveI : Subsingleton (H2 (quotRep ρ U U')) := H2_quotientToInvariants_subsingleton_of_zl_quotient l _ hρU hl _ κ hκ hs hk`. Establish `hc : IsClosed (U'.subgroupOf U : Set U)`.

Rewrite using `[← hk]`. Conclude with `isClosed_singleton.preimage hκ`. Establish `hc' : IsClosed (U' : Set G)`. Use `hU.isClosedEmbedding_subtypeVal.isClosedMap _ hc` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Conclude with `⟨fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩, fun ⟨y, hy, e⟩ => e ▸ hy⟩`. Take `⟨tg, htg⟩` from `transg R G M ρ hρ U' U h hU hc'`. Introduce `x hx`. Establish `h0 : (Submodule.Quotient.mk ⟨x, hx⟩ : resCoker ρ h) = 0` using `htg (Subsingleton.elim _ _)`.

Conclude with `Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h0)`.
-/
theorem UpperTheory.V.Base.resZl :
    ∀ (l : ℕ) [Fact l.Prime], ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G], ContAction ρ → (∀ m : M, ∃ n : ℕ, l ^ n • m = 0) →
      ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsClosed (U : Set G) → ∀ κ : U →* Multiplicative ℤ_[l], Continuous κ →
      Function.Surjective κ → κ.ker = U'.subgroupOf U → invariantsUnderSubgroupH1 ρ U U' ≤ LinearMap.range (resU ρ h) := by
  intro l _ R G M _ _ _ _ _ _ _ _ _ _ ρ _ _ _ hρ hl U' U _ h hU κ hκ hs hk
  haveI : CompactSpace U := isCompact_iff_compactSpace.1 hU.isCompact
  have hρU : ReciprocityTheory.Gal.ContAction (ρ.comp U.subtype : Representation R U M) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  haveI : Subsingleton (H2 (quotRep ρ U U')) := H2_quotientToInvariants_subsingleton_of_zl_quotient l _ hρU hl _ κ hκ hs hk
  have hc : IsClosed (U'.subgroupOf U : Set U) := by
    rw [← hk]
    exact isClosed_singleton.preimage hκ
  have hc' : IsClosed (U' : Set G) := by
    have := hU.isClosedEmbedding_subtypeVal.isClosedMap _ hc
    convert this using 1
    ext x
    exact ⟨fun hx => ⟨⟨x, h hx⟩, hx, rfl⟩, fun ⟨y, hy, e⟩ => e ▸ hy⟩
  obtain ⟨tg, htg⟩ := transg R G M ρ hρ U' U h hU hc'
  intro x hx
  have h0 : (Submodule.Quotient.mk ⟨x, hx⟩ : resCoker ρ h) = 0 := htg (Subsingleton.elim _ _)
  exact Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
