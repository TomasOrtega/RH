import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.FinChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V UpperTheory.V.Fr UpperTheory.V.GC

/- English proof (translation)
Use `⟨∏ v ∈ S, Ideal.absNorm v.asIdeal, Finset.prod_ne_zero_iff.2 fun v _ h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 F) => Ideal.absNorm v.asIdeal) hv`. Rewrite using `[hc, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)`.
-/
private theorem pG_nat {F : Type} [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ v ∈ S, ((N : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  refine ⟨∏ v ∈ S, Ideal.absNorm v.asIdeal, Finset.prod_ne_zero_iff.2 fun v _ h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h),
    fun v hv => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun v : HeightOneSpectrum (𝓞 F) => Ideal.absNorm v.asIdeal) hv
  rw [hc, Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `x`. Establish `ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (φ.ker : Set H))` using `h.preimage (by fun_prop)`. Use `filter_upwards [ho.mem_nhds (show x ∈ (fun y => x⁻¹ * y) ⁻¹' (φ.ker : Set H) by simp)] with y hy`. Establish `: φ (x⁻¹ * y) = 1` using `hy`.

Rewrite `this` using `[map_mul, map_inv, inv_mul_eq_one]`. Conclude with `this.symm`.
-/
private theorem pG_lc {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Group M]
    (φ : H →* M) (h : IsOpen (φ.ker : Set H)) : IsLocallyConstant φ := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have ho : IsOpen ((fun y => x⁻¹ * y) ⁻¹' (φ.ker : Set H)) := h.preimage (by fun_prop)
  filter_upwards [ho.mem_nhds (show x ∈ (fun y => x⁻¹ * y) ⁻¹' (φ.ker : Set H) by simp)] with y hy
  have : φ (x⁻¹ * y) = 1 := hy
  rw [map_mul, map_inv, inv_mul_eq_one] at this
  exact this.symm

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l hl S K Γ _ _ _ _ _ _ π hL H hH`. Use `haveI : IsGalois F Ω := {}`. Use `haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `haveI : NeZero l := ⟨hl.out.ne_zero⟩`.

Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω l`. Take `⟨N, hN, hNS⟩` from `pG_nat S`. Set `V : Subgroup (G F Ω)` to `(H.comap π ⊓ K) ⊓ MulAction.stabilizer (G F Ω) ζ`. Establish `hVo : IsOpen (V : Set (G F Ω))` using `((hH.preimage hL.cont).inter hL.isOpen).inter (stabilizer_isOpen_of_isIntegral ζ)`. Set `E : IntermediateField F Ω` to `IntermediateField.fixedField V`.

Establish `hE : E.fixingSubgroup = V` using `InfiniteGalois.fixingSubgroup_fixedField ⟨V, V.isClosed_of_isOpen hVo⟩`. Use `haveI : FiniteDimensional F E := (InfiniteGalois.isOpen_iff_finite E).1 (by rw [← hE] at hVo; exact hVo)`. Use `haveI : NumberField E := NumberField.of_module_finite F E`. Establish `hmem : ∀ σ : G E Ω, Base.galEmb F E Ω σ ∈ V` using `fun σ => by`. Rewrite using `[← hE, IntermediateField.mem_fixingSubgroup_iff]`.

Conclude with `fun x hx => σ.commutes ⟨x, hx⟩`. Establish `hgal : V ≤ Base.galOf F E Ω` using `fun u hu x => x.2 ⟨u, hu⟩`. Establish `hζE : ζ ∈ E` using `fun v => v.2.2`. Establish `hζ' : IsPrimitiveRoot (⟨ζ, hζE⟩ : E) l` using `IsPrimitiveRoot.of_map_of_injective (f := algebraMap E Ω) hζ (algebraMap E Ω).injective`. Use `haveI := (Kum.finChar E Ω l N _ hl.out.ne_zero hN hζ').to_subtype`.

Set `e : G E Ω →* H` to `(π.comp (Base.galEmb F E Ω)).codRestrict H fun σ => (hmem σ).1.1`. Establish `he : Continuous e` using `(hL.cont.comp (Base.galEmbTop F E Ω).1.continuous).subtype_mk _`. Establish `hker : ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F` using `E) A, e g = 1 := by`. Introduce `A hA g hg`. Distinguish the cases in `hT : A = ⊤`.

Substitute `hT` using the available equality. Rewrite `hg` using `[(Kum.placeDict E Ω).1, Subgroup.mem_bot]`. Rewrite using `[hg, map_one]`. Take `⟨v, hv⟩` from `(Kum.placeDict F Ω).2.1 A hT`. Establish `hvS : v ∉ S` using `fun h => hA (((Kum.placeDict F Ω).2.2.2 A v N hv).2 (hNS v h))`.

Establish `hI : Base.galEmb F E Ω g ∈ Ine (F` using `F) A := ⟨hg.1, hg.2⟩`. Establish `: Base.galEmb F E Ω g ∈ π.ker`. Rewrite using `[hL.ker]`. Use `Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_iUnion]`.

Conclude with `⟨v, hvS, A, hv, hI, (hmem g).1.2⟩`. Conclude with `Subtype.ext this`. Use `haveI : Finite (G F Ω ⧸ V) := V.quotient_finite_of_isOpen hVo`. Establish `hfin : Finite (H ⧸ e.range)` using `by haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient`. Establish `h1 : (V.map π).FiniteIndex` using `⟨fun h => Subgroup.FiniteIndex.index_ne_zero (H := V) (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_map_dvd V hL.onto))⟩`.

Establish `h2 : (V.map π).subgroupOf H ≤ e.range`. Introduce and unpack `x ⟨u, hu, hx⟩`. Conclude with `⟨Kum.toGal E hgal ⟨u, hu⟩, Subtype.ext hx⟩`. Use `haveI := Subgroup.finiteIndex_of_le h2`. Use `infer_instance`.

Use `Finite.of_injective (β := {φ : G E Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧ ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := E) A, φ g = 0} × (H ⧸ e.range → Multiplicative (ZMod l))) (fun φ => (⟨fun g => Multiplicative.toAdd (φ.1 (e …` and prove the remaining obligations. Rewrite using `[hker A hA g hg, map_one, toAdd_one]⟩, fun q => φ.1 q.out)) ?_`. Introduce `φ ψ h`. Establish `h1 : ∀ g, φ.1 (e g) = ψ.1 (e g)` using `fun g => Multiplicative.toAdd.injective (congrFun (congrArg Subtype.val (congrArg Prod.fst h)) g)`. Establish `h2 : ∀ q : H ⧸ e.range, φ.1 q.out = ψ.1 q.out` using `congrFun (congrArg Prod.snd h)`.

Use `Subtype.ext (MonoidHom.ext fun x => ?_)` and prove the remaining obligations. Take `⟨⟨_, g, rfl⟩, hg⟩` from `QuotientGroup.mk_out_eq_mul e.range x`. Establish `h3` using `h2 (QuotientGroup.mk x)`. Rewrite `h3` using `[hg, map_mul, map_mul, h1]`. Conclude with `mul_right_cancel h3`.
-/
theorem UpperTheory.V.GC.phiGam :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))) (K : Subgroup (G F Ω)) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] (π : G F Ω →* Γ), GLink l S K π → Alg.PhiCond Γ l := by
  intro F Ω _ _ _ _ _ l hl S K Γ _ _ _ _ _ _ π hL H hH
  haveI : IsGalois F Ω := {}
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero l := ⟨hl.out.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω l
  obtain ⟨N, hN, hNS⟩ := pG_nat S
  let V : Subgroup (G F Ω) := (H.comap π ⊓ K) ⊓ MulAction.stabilizer (G F Ω) ζ
  have hVo : IsOpen (V : Set (G F Ω)) :=
    ((hH.preimage hL.cont).inter hL.isOpen).inter (stabilizer_isOpen_of_isIntegral ζ)
  let E : IntermediateField F Ω := IntermediateField.fixedField V
  have hE : E.fixingSubgroup = V :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨V, V.isClosed_of_isOpen hVo⟩
  haveI : FiniteDimensional F E := (InfiniteGalois.isOpen_iff_finite E).1 (by rw [← hE] at hVo; exact hVo)
  haveI : NumberField E := NumberField.of_module_finite F E
  have hmem : ∀ σ : G E Ω, Base.galEmb F E Ω σ ∈ V := fun σ => by
    rw [← hE, IntermediateField.mem_fixingSubgroup_iff]
    exact fun x hx => σ.commutes ⟨x, hx⟩
  have hgal : V ≤ Base.galOf F E Ω := fun u hu x => x.2 ⟨u, hu⟩
  have hζE : ζ ∈ E := fun v => v.2.2
  have hζ' : IsPrimitiveRoot (⟨ζ, hζE⟩ : E) l :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap E Ω) hζ (algebraMap E Ω).injective
  haveI := (Kum.finChar E Ω l N _ hl.out.ne_zero hN hζ').to_subtype
  let e : G E Ω →* H := (π.comp (Base.galEmb F E Ω)).codRestrict H fun σ => (hmem σ).1.1
  have he : Continuous e := (hL.cont.comp (Base.galEmbTop F E Ω).1.continuous).subtype_mk _
  have hker : ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := E) A, e g = 1 := by
    intro A hA g hg
    by_cases hT : A = ⊤
    · subst hT
      rw [(Kum.placeDict E Ω).1, Subgroup.mem_bot] at hg
      rw [hg, map_one]
    · obtain ⟨v, hv⟩ := (Kum.placeDict F Ω).2.1 A hT
      have hvS : v ∉ S := fun h => hA (((Kum.placeDict F Ω).2.2.2 A v N hv).2 (hNS v h))
      have hI : Base.galEmb F E Ω g ∈ Ine (F := F) A := ⟨hg.1, hg.2⟩
      have : Base.galEmb F E Ω g ∈ π.ker := by
        rw [hL.ker]
        refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ?_)
        simp only [Set.mem_iUnion]
        exact ⟨v, hvS, A, hv, hI, (hmem g).1.2⟩
      exact Subtype.ext this
  haveI : Finite (G F Ω ⧸ V) := V.quotient_finite_of_isOpen hVo
  have hfin : Finite (H ⧸ e.range) := by
    haveI : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have h1 : (V.map π).FiniteIndex :=
      ⟨fun h => Subgroup.FiniteIndex.index_ne_zero (H := V)
        (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_map_dvd V hL.onto))⟩
    have h2 : (V.map π).subgroupOf H ≤ e.range := by
      rintro x ⟨u, hu, hx⟩
      exact ⟨Kum.toGal E hgal ⟨u, hu⟩, Subtype.ext hx⟩
    haveI := Subgroup.finiteIndex_of_le h2
    infer_instance
  refine Finite.of_injective (β := {φ : G E Ω → ZMod l | IsLocallyConstant φ ∧ (∀ a b, φ (a * b) = φ a + φ b) ∧
      ∀ A : ValuationSubring Ω, ¬ A.valuation (N : Ω) < 1 → ∀ g ∈ Ine (F := E) A, φ g = 0} ×
      (H ⧸ e.range → Multiplicative (ZMod l)))
    (fun φ => (⟨fun g => Multiplicative.toAdd (φ.1 (e g)), ((pG_lc φ.1 φ.2).comp_continuous he).comp _,
      fun a b => by simp only [map_mul, toAdd_mul], fun A hA g hg => by
        show Multiplicative.toAdd (φ.1 (e g)) = 0
        rw [hker A hA g hg, map_one, toAdd_one]⟩, fun q => φ.1 q.out)) ?_
  intro φ ψ h
  have h1 : ∀ g, φ.1 (e g) = ψ.1 (e g) := fun g =>
    Multiplicative.toAdd.injective (congrFun (congrArg Subtype.val (congrArg Prod.fst h)) g)
  have h2 : ∀ q : H ⧸ e.range, φ.1 q.out = ψ.1 q.out := congrFun (congrArg Prod.snd h)
  refine Subtype.ext (MonoidHom.ext fun x => ?_)
  obtain ⟨⟨_, g, rfl⟩, hg⟩ := QuotientGroup.mk_out_eq_mul e.range x
  have h3 := h2 (QuotientGroup.mk x)
  rw [hg, map_mul, map_mul, h1] at h3
  exact mul_right_cancel h3
