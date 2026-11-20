import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

open ReciprocityTheory.Gal UpperTheory.V.Base

/- English proof (translation)
Establish `hmem : ∀ u' : U', φ u' ∈ U` using `fun u' => h ▸ Subgroup.mem_map_of_mem φ u'.2`. Set `f : U' →* U` to `{ toFun := fun u' => ⟨φ u', hmem u'⟩ map_one' := by ext; simp map_mul' := by intro a b; ext; simp }`. Establish `hinj : Function.Injective f`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `hφ.injective` to reduce the goal to its premises. Conclude with `congrArg Subtype.val hab`. Establish `hsurj : Function.Surjective f`. Introduce and unpack `⟨g, hg⟩`. Rewrite `hg` using `[← h]`.

Take `⟨x, hx, rfl⟩` from `Subgroup.mem_map.mp hg`. Conclude with `⟨⟨x, hx⟩, rfl⟩`. Set `e : U' ≃* U` to `MulEquiv.ofBijective f ⟨hinj, hsurj⟩`. Establish `he : ∀ u' : U', ((e u' : U) : G) = φ u'` using `fun _ => rfl`. Use `⟨e, he, ?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Continuous (fun u' : U' => (⟨φ u', hmem u'⟩ : U))`. Conclude with `(hφ.continuous.comp continuous_subtype_val).subtype_mk _`. Rewrite using `[Topology.IsEmbedding.subtypeVal.isInducing.continuous_iff, hφ.isInducing.continuous_iff]`. Establish `hc : (⇑φ ∘ Subtype.val ∘ ⇑e.symm) = (Subtype.val : U → G)`. Use function extensionality and compare the values at `u`.

Use `he (e.symm u)` as an intermediate fact. Rewrite `this` using `[e.apply_symm_apply]`. Conclude with `this.symm`. Rewrite using `[hc]`. Conclude with `continuous_subtype_val`.
-/
private theorem exists_continuous_mulEquiv_of_map_embedding {G G' : Type} [Group G] [Group G'] [TopologicalSpace G]
    [TopologicalSpace G'] (φ : G' →* G) (hφ : Topology.IsEmbedding φ) (U' : Subgroup G')
    (U : Subgroup G) (h : U'.map φ = U) :
    ∃ e : U' ≃* U, (∀ u' : U', ((e u' : U) : G) = φ u') ∧ Continuous e ∧ Continuous e.symm := by
  have hmem : ∀ u' : U', φ u' ∈ U := fun u' => h ▸ Subgroup.mem_map_of_mem φ u'.2
  let f : U' →* U :=
    { toFun := fun u' => ⟨φ u', hmem u'⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hφ.injective
    exact congrArg Subtype.val hab
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    rw [← h] at hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : U' ≃* U := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have he : ∀ u' : U', ((e u' : U) : G) = φ u' := fun _ => rfl
  refine ⟨e, he, ?_, ?_⟩
  · change Continuous (fun u' : U' => (⟨φ u', hmem u'⟩ : U))
    exact (hφ.continuous.comp continuous_subtype_val).subtype_mk _
  · rw [Topology.IsEmbedding.subtypeVal.isInducing.continuous_iff, hφ.isInducing.continuous_iff]
    have hc : (⇑φ ∘ Subtype.val ∘ ⇑e.symm) = (Subtype.val : U → G) := by
      funext u
      have := he (e.symm u)
      rw [e.apply_symm_apply] at this
      exact this.symm
    rw [hc]
    exact continuous_subtype_val

/- English proof (translation)
Introduce `R G M _ _ _ _ _ _ _ _ _ _ ρ G' _ _ φ hφ U' U hU 𝒟`. Take `⟨e, he, hec, hesc⟩` from `exists_continuous_mulEquiv_of_map_embedding φ hφ U' U hU`. Establish `key : ∀ g : U, φ ((e.symm g : U') : G') = g` using `fun g => by`. Rewrite using `[← he, e.apply_symm_apply]`. Set `A : Representation R U' M` to `(ρ.comp φ).comp U'.subtype`.

Set `B : Representation R U M` to `ρ.comp U.subtype`. Set `F : H1 B →ₗ[R] H1 A` to `pairH1DecompositionMap B A e.toMonoidHom hec LinearMap.id continuous_id (fun g m => by`. Simplify using `only [A, B, LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, he])`. Set `E : H1 A →ₗ[R] H1 B` to `pairH1DecompositionMap A B e.symm.toMonoidHom hesc LinearMap.id continuous_id (fun g m => by`. Simplify using `only [A, B, LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, key])`.

Establish `hEF : E ∘ₗ F = LinearMap.id`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Simplify using `only [E, F, LinearMap.comp_apply, pairH1DecompositionMap, Submodule.mapQ_apply, LinearMap.id_apply]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Simplify using `[compatiblePairCocycles1]`. Establish `hFE : F ∘ₗ E = LinearMap.id`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Simplify using `only [E, F, LinearMap.comp_apply, pairH1DecompositionMap, Submodule.mapQ_apply, LinearMap.id_apply]`. Use `congr 1`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Simplify using `[compatiblePairCocycles1]`. Set `L : H1 A ≃ₗ[R] H1 B` to `LinearEquiv.ofLinear E F hEF hFE`. Establish `hmap : (LocSel (ρ.comp φ : Representation R G' M) U' (Subgroup.comap φ '' 𝒟)).map (L : H1 A →ₗ[R] H1 B) = LocSel ρ U 𝒟`.

Use extensionality with `x`. Take `⟨z, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[Submodule.mem_map_equiv]`. Simplify using `only [L, LinearEquiv.ofLinear_symm_apply, F, pairH1DecompositionMap, Submodule.mapQ_apply]`. Rewrite using `[mk_mem_locSel, mk_mem_locSel]`.

Prove the components needed by the constructor for the conclusion. Introduce `hyp D hD`. Take `⟨m, hm⟩` from `hyp _ ⟨D, hD, rfl⟩`. Use `⟨m, fun u hu => ?_⟩` and prove the remaining obligations. Establish `h1` using `hm (e.symm u) (by rw [Subgroup.mem_comap, key]; exact hu)`.

Simplify `h1` using `[compatiblePairCocycles1, key]`. Introduce and unpack `hyp D' ⟨D, hD, rfl⟩`. Take `⟨m, hm⟩` from `hyp D hD`. Use `⟨m, fun u' hu' => ?_⟩` and prove the remaining obligations. Establish `h1` using `hm (e u') (by rw [he]; exact hu')`.

Rewrite `h1` using `[he]`. Simplify `h1` using `[compatiblePairCocycles1, he]`. Use `⟨L.ofSubmodules _ _ hmap, ?_⟩` and prove the remaining obligations. Introduce `z' z hz' hzz`. Rewrite using `[LinearEquiv.ofSubmodules_apply]`.

Simplify using `only [L, LinearEquiv.ofLinear_apply, E, pairH1DecompositionMap, Submodule.mapQ_apply]`. Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `u`. Simplify using `only [compatiblePairCocycles1]`.

Conclude with `(hzz (e.symm u) u (key u)).symm`.
-/
theorem UpperTheory.V.Base.selTransport :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (G' : Type) [Group G'] [TopologicalSpace G'] (φ : G' →* G), Topology.IsEmbedding φ →
      ∀ (U' : Subgroup G') (U : Subgroup G), U'.map φ = U → ∀ 𝒟 : Set (Subgroup G),
      ∃ Φ : LocSel (ρ.comp φ : Representation R G' M) U' (Subgroup.comap φ '' 𝒟) ≃ₗ[R] LocSel ρ U 𝒟,
        ∀ (z' : Z1U (ρ.comp φ : Representation R G' M) U') (z : Z1U ρ U) hz', (∀ (u' : U') (u : U), φ u' = u → z.1 u = z'.1 u') →
          (Φ ⟨Submodule.Quotient.mk z', hz'⟩ : H1U ρ U) = Submodule.Quotient.mk z := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ G' _ _ φ hφ U' U hU 𝒟
  obtain ⟨e, he, hec, hesc⟩ := exists_continuous_mulEquiv_of_map_embedding φ hφ U' U hU
  have key : ∀ g : U, φ ((e.symm g : U') : G') = g := fun g => by
    rw [← he, e.apply_symm_apply]
  let A : Representation R U' M := (ρ.comp φ).comp U'.subtype
  let B : Representation R U M := ρ.comp U.subtype
  let F : H1 B →ₗ[R] H1 A :=
    pairH1DecompositionMap B A e.toMonoidHom hec LinearMap.id continuous_id (fun g m => by
      simp only [A, B, LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, he])
  let E : H1 A →ₗ[R] H1 B :=
    pairH1DecompositionMap A B e.symm.toMonoidHom hesc LinearMap.id continuous_id (fun g m => by
      simp only [A, B, LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, key])
  have hEF : E ∘ₗ F = LinearMap.id := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [E, F, LinearMap.comp_apply, pairH1DecompositionMap, Submodule.mapQ_apply, LinearMap.id_apply]
    congr 1
    apply Subtype.ext
    funext g
    simp [compatiblePairCocycles1]
  have hFE : F ∘ₗ E = LinearMap.id := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [E, F, LinearMap.comp_apply, pairH1DecompositionMap, Submodule.mapQ_apply, LinearMap.id_apply]
    congr 1
    apply Subtype.ext
    funext g
    simp [compatiblePairCocycles1]
  let L : H1 A ≃ₗ[R] H1 B := LinearEquiv.ofLinear E F hEF hFE
  have hmap : (LocSel (ρ.comp φ : Representation R G' M) U' (Subgroup.comap φ '' 𝒟)).map
      (L : H1 A →ₗ[R] H1 B) = LocSel ρ U 𝒟 := by
    ext x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mem_map_equiv]
    simp only [L, LinearEquiv.ofLinear_symm_apply, F, pairH1DecompositionMap, Submodule.mapQ_apply]
    rw [mk_mem_locSel, mk_mem_locSel]
    constructor
    · intro hyp D hD
      obtain ⟨m, hm⟩ := hyp _ ⟨D, hD, rfl⟩
      refine ⟨m, fun u hu => ?_⟩
      have h1 := hm (e.symm u) (by rw [Subgroup.mem_comap, key]; exact hu)
      simpa [compatiblePairCocycles1, key] using h1
    · rintro hyp D' ⟨D, hD, rfl⟩
      obtain ⟨m, hm⟩ := hyp D hD
      refine ⟨m, fun u' hu' => ?_⟩
      have h1 := hm (e u') (by rw [he]; exact hu')
      rw [he] at h1
      simpa [compatiblePairCocycles1, he] using h1
  refine ⟨L.ofSubmodules _ _ hmap, ?_⟩
  intro z' z hz' hzz
  rw [LinearEquiv.ofSubmodules_apply]
  simp only [L, LinearEquiv.ofLinear_apply, E, pairH1DecompositionMap, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  funext u
  simp only [compatiblePairCocycles1]
  exact (hzz (e.symm u) u (key u)).symm
