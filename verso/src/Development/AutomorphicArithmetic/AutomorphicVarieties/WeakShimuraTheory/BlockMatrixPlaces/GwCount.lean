import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.UrCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PlusCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GwIneq
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.SelToZc
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.PlaceSet
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.GammaOneGammaZeroHomogeneousCocyclesFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

/- English proof (translation)
Introduce `hC Ω _ _ _ l hl S c s B hP R M _ _ _ _ ρ r hr hlc K hK hun hc hs P hPs`. Establish `hfin` using `zcFin hC.gf S c s B hP R M ρ r hr hlc K hK hun (P : Set M)`. Use `haveI : Finite (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) (P : Set M)) := hfin`. Take `⟨S', Av, v0, hS', hAv, hB, hv0, hNS⟩` from `placeSet (l := l) S B hP.prime hP.mem hP.ovl`. Substitute `hB` using the available equality.

Establish `hr1 : ∀ m : M, (l ^ (r + 1)) • m = 0` using `fun m => by rw [pow_succ', mul_smul, hr, smul_zero]`. Use `haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hl.out.ne_zero⟩`. Use `haveI : Module (ZMod (l ^ (r + 1))) M := AddCommGroup.zmodModule hr1`. Use `letI : TopologicalSpace M := ⊥`. Use `haveI : DiscreteTopology M := ⟨rfl⟩`.

Establish `hcl : IsClosed (ρ.ker : Set (G ℚ Ω))`. Establish `e : (ρ.ker : Set (G ℚ Ω)) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m}`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]`. Conclude with `⟨fun h m => by rw [h]; rfl, fun h => LinearMap.ext h⟩`.

Rewrite using `[e]`. Conclude with `isClosed_iInter fun m => ((hlc m).isClopen_fiber m).1`. Establish `hN` using `hNS ρ.ker inferInstance hcl fun A hA => (hun A hA).trans hK`. Set `ρ1 : Representation (ZMod (l ^ (r + 1))) (G ℚ Ω) M` to `{ toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap (l ^ (r + 1)) map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by`. Rewrite using `[map_mul]`.

Use `rfl }`. Set `σ : Representation (ZMod (l ^ (r + 1))) (GS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ)))) M` to `QuotientGroup.lift _ ρ1 fun g hg => LinearMap.ext fun m => show ρ g m = m by`. Rewrite using `[show ρ g = 1 from hN hg]`. Both sides reduce to the same expression. Establish `hσ : ∀ g m, σ (toGS Ω _ g) m = ρ g m` using `fun _ _ => rfl`.

Establish `hcont : ContAction σ`. Use `continuous_prod_of_discrete_right.2 fun m => ?_` and prove the remaining obligations. Conclude with `(QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (hlc m).continuous`. Establish `hloc : ∀ v, ContAction (σ.comp (locFam S' Av v))` using `fun v => Continuous.comp (f := fun p : Dec (F := ℚ) (Av v) × M => (locFam S' Av v p.1, p.2)) hcont (((continuous_locFam S' Av v).comp continuous_fst).prodMk continuous_snd)`. Set `P' : Submodule (ZMod (l ^ (r + 1))) M` to `AddSubgroup.toZModSubmodule _ P.toAddSubgroup`.

Take `⟨L0, hL0, hL0'⟩` from `plusCard hC.loc.lf hC.loc.le (r + 1) M (Av v0) v0.1 (σ.comp (locFam S' Av v0)) r.succ_pos (hAv v0) hv0 (hloc v0) P' (fun h x hx => hPs h.1 h.2 x hx) ⟨⟨s, hP.dec⟩, hs⟩`. Set `L : LocCond σ (locFam S' Av)` to `Function.update (fun v => H1ur (σ.comp (locFam S' Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v)))) v0 L0`. Establish `hLv0 : L v0 = L0` using `Function.update_self ..`. Establish `hLv : ∀ v, v ≠ v0 → L v = H1ur (σ.comp (locFam S' Av v)) ((Ine (F` using `ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v))) := fun v hv => Function.update_of_ne hv ..`. Establish `h1` using `gwIneq hC.gf hC.gw (r + 1) M S' σ r.succ_pos hP.odd hS' hcont c hP.cc hc Av hAv v0 s hP.dec hP.cyc hs L fun v hv => by`.

Take `⟨φ, -, h1, h2⟩` from `GC.decZhat ℚ Ω v.1 (Av v) (hAv v)`. Rewrite using `[hLv v hv, urCard _ _ _ _ (hloc v) _ φ h1 h2]`. Establish `h2 : Function.Bijective fun m : M => m + m`. Use `Finite.injective_iff_bijective.1 ((injective_iff_map_eq_zero (AddMonoidHom.id M + AddMonoidHom.id M)).2 ?_)` and prove the remaining obligations. Introduce `m hm`.

Establish `hm2 : 2 • m = 0` using `by rw [two_smul]; exact hm`. Establish `hco : Nat.Coprime 2 (l ^ r)` using `((Nat.coprime_primes Nat.prime_two hl.out).2 hP.odd.symm).pow_right _`. Use `Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hm2) (addOrderOf_dvd_of_nsmul_eq_zero (hr m))` as an intermediate fact. Rewrite `this` using `[hco.gcd_eq_one, Nat.dvd_one]`. Conclude with `AddMonoid.addOrderOf_eq_one_iff.1 this`.

Take `⟨f, hf⟩` from `selToZc (l := l) _ M S' σ hcont h2 c hc Av hAv v0 hv0 (P : Set M) K (fun g hg m => show ρ g m = m by rw [show ρ g = 1 from hK hg]; rfl) L (fun v hv => (hLv v hv).le) (fun z hz => hL0' z (hLv0 ▸ hz))`. Rewrite `h1` using `[hLv0]`. Conclude with `hL0.trans (h1.trans (Nat.card_le_card_of_injective f hf))`.
-/
theorem UpperTheory.V.Ws.Bl.gwCount :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (S : Finset ℕ) (c s : G ℚ Ω) (B : ValuationSubring Ω), Pos l S c s B → ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R (G ℚ Ω) M) (r : ℕ), (∀ m : M, (l ^ r) • m = 0) → (∀ m, IsLocallyConstant fun g => ρ g m) →
          ∀ K : Subgroup (G ℚ Ω), K ≤ ρ.ker → (∀ A, Raw.Away S A → Ine (F := ℚ) A ≤ K) → (∀ m, ρ c m = -m) → (Function.Bijective fun m => ρ s m - m) →
          ∀ P : Submodule R M, (∀ h ∈ Dec (F := ℚ) B, ∀ x ∈ P, ρ h x ∈ P) → Nat.card P ≤ Nat.card (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) (P : Set M)) := by
  classical
  intro hC Ω _ _ _ l hl S c s B hP R M _ _ _ _ ρ r hr hlc K hK hun hc hs P hPs
  have hfin := zcFin hC.gf S c s B hP R M ρ r hr hlc K hK hun (P : Set M)
  haveI : Finite (Zc (fun g m => ρ g m) c (neSet l K) (Dec (F := ℚ) B) (P : Set M)) := hfin
  obtain ⟨S', Av, v0, hS', hAv, hB, hv0, hNS⟩ := placeSet (l := l) S B hP.prime hP.mem hP.ovl
  subst hB
  have hr1 : ∀ m : M, (l ^ (r + 1)) • m = 0 := fun m => by rw [pow_succ', mul_smul, hr, smul_zero]
  haveI : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  haveI : Module (ZMod (l ^ (r + 1))) M := AddCommGroup.zmodModule hr1
  letI : TopologicalSpace M := ⊥
  haveI : DiscreteTopology M := ⟨rfl⟩
  have hcl : IsClosed (ρ.ker : Set (G ℚ Ω)) := by
    have e : (ρ.ker : Set (G ℚ Ω)) = ⋂ m : M, (fun g => ρ g m) ⁻¹' {m} := by
      ext g
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h m => by rw [h]; rfl, fun h => LinearMap.ext h⟩
    rw [e]
    exact isClosed_iInter fun m => ((hlc m).isClopen_fiber m).1
  have hN := hNS ρ.ker inferInstance hcl fun A hA => (hun A hA).trans hK
  let ρ1 : Representation (ZMod (l ^ (r + 1))) (G ℚ Ω) M :=
    { toFun := fun g => (ρ g).toAddMonoidHom.toZModLinearMap (l ^ (r + 1))
      map_one' := LinearMap.ext fun m => show ρ 1 m = m by rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => show ρ (g * h) m = ρ g (ρ h m) by
        rw [map_mul]; rfl }
  let σ : Representation (ZMod (l ^ (r + 1))) (GS Ω (S' : Set (HeightOneSpectrum (𝓞 ℚ)))) M :=
    QuotientGroup.lift _ ρ1 fun g hg => LinearMap.ext fun m => show ρ g m = m by
      rw [show ρ g = 1 from hN hg]; rfl
  have hσ : ∀ g m, σ (toGS Ω _ g) m = ρ g m := fun _ _ => rfl
  have hcont : ContAction σ := by
    refine continuous_prod_of_discrete_right.2 fun m => ?_
    exact (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (hlc m).continuous
  have hloc : ∀ v, ContAction (σ.comp (locFam S' Av v)) := fun v =>
    Continuous.comp (f := fun p : Dec (F := ℚ) (Av v) × M => (locFam S' Av v p.1, p.2)) hcont
      (((continuous_locFam S' Av v).comp continuous_fst).prodMk continuous_snd)
  let P' : Submodule (ZMod (l ^ (r + 1))) M := AddSubgroup.toZModSubmodule _ P.toAddSubgroup
  obtain ⟨L0, hL0, hL0'⟩ := plusCard hC.loc.lf hC.loc.le (r + 1) M (Av v0) v0.1 (σ.comp (locFam S' Av v0))
    r.succ_pos (hAv v0) hv0 (hloc v0) P' (fun h x hx => hPs h.1 h.2 x hx) ⟨⟨s, hP.dec⟩, hs⟩
  let L : LocCond σ (locFam S' Av) := Function.update
    (fun v => H1ur (σ.comp (locFam S' Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v)))) v0 L0
  have hLv0 : L v0 = L0 := Function.update_self ..
  have hLv : ∀ v, v ≠ v0 →
      L v = H1ur (σ.comp (locFam S' Av v)) ((Ine (F := ℚ) (Av v)).subgroupOf (Dec (F := ℚ) (Av v))) :=
    fun v hv => Function.update_of_ne hv ..
  have h1 := gwIneq hC.gf hC.gw (r + 1) M S' σ r.succ_pos hP.odd hS' hcont c hP.cc hc Av hAv v0 s hP.dec hP.cyc hs L
    fun v hv => by
      obtain ⟨φ, -, h1, h2⟩ := GC.decZhat ℚ Ω v.1 (Av v) (hAv v)
      rw [hLv v hv, urCard _ _ _ _ (hloc v) _ φ h1 h2]
  have h2 : Function.Bijective fun m : M => m + m := by
    refine Finite.injective_iff_bijective.1 ((injective_iff_map_eq_zero (AddMonoidHom.id M + AddMonoidHom.id M)).2 ?_)
    intro m hm
    have hm2 : 2 • m = 0 := by rw [two_smul]; exact hm
    have hco : Nat.Coprime 2 (l ^ r) :=
      ((Nat.coprime_primes Nat.prime_two hl.out).2 hP.odd.symm).pow_right _
    have := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hm2) (addOrderOf_dvd_of_nsmul_eq_zero (hr m))
    rw [hco.gcd_eq_one, Nat.dvd_one] at this
    exact AddMonoid.addOrderOf_eq_one_iff.1 this
  obtain ⟨f, hf⟩ := selToZc (l := l) _ M S' σ hcont h2 c hc Av hAv v0 hv0 (P : Set M) K
    (fun g hg m => show ρ g m = m by rw [show ρ g = 1 from hK hg]; rfl) L (fun v hv => (hLv v hv).le)
    (fun z hz => hL0' z (hLv0 ▸ hz))
  rw [hLv0] at h1
  exact hL0.trans (h1.trans (Nat.card_le_card_of_injective f hf))
