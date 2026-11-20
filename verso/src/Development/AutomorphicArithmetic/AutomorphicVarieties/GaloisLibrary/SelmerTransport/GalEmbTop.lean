import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ConjStableShaFam

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hs`. Take `⟨F, hF, hFs⟩` from `(krullTopology_mem_nhds_one_iff K L s).mp hs`. Set `b` to `Module.finBasis K F`. Use `⟨Finset.univ.image (fun i => (b i : L)), fun σ hσ => hFs ?_⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `y hy`. Establish `hb : ∀ i, σ (b i : L) = b i` using `fun i => hσ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))`. Establish `hy' : y = ∑ i, (b.repr ⟨y, hy⟩ i) • (b i : L)`. Establish `h` using `congrArg (fun z : F => (z : L)) (b.sum_repr ⟨y, hy⟩)`.

Simplify using `only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h`. Conclude with `h.symm`. Rewrite using `[hy', map_sum]`. Simplify using `[map_smul, hb]`. Introduce and unpack `⟨S, hS⟩`.

Use `Filter.mem_of_superset ?_ hS` and prove the remaining obligations. Establish `: {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} = ⋂ x ∈ S, (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K))`. Use extensionality with `σ`. Simplify using `[MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`. Rewrite using `[this]`.

Conclude with `(isOpen_biInter_finset fun x _ => stabilizer_isOpen_of_isIntegral x).mem_nhds (by simp)`.
-/
private theorem mem_nhds_one_gal_iff_exists_finset_fixing (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L]
    (s : Set Gal(L/K)) :
    s ∈ nhds (1 : Gal(L/K)) ↔ ∃ S : Finset L, {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} ⊆ s := by
  classical
  constructor
  · intro hs
    obtain ⟨F, hF, hFs⟩ := (krullTopology_mem_nhds_one_iff K L s).mp hs
    let b := Module.finBasis K F
    refine ⟨Finset.univ.image (fun i => (b i : L)), fun σ hσ => hFs ?_⟩
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have hb : ∀ i, σ (b i : L) = b i := fun i => hσ _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    have hy' : y = ∑ i, (b.repr ⟨y, hy⟩ i) • (b i : L) := by
      have h := congrArg (fun z : F => (z : L)) (b.sum_repr ⟨y, hy⟩)
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
      exact h.symm
    rw [hy', map_sum]
    simp [map_smul, hb]
  · rintro ⟨S, hS⟩
    refine Filter.mem_of_superset ?_ hS
    have : {σ : Gal(L/K) | ∀ x ∈ S, σ x = x} =
        ⋂ x ∈ S, (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
      ext σ
      simp [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
    rw [this]
    exact (isOpen_biInter_finset fun x _ => stabilizer_isOpen_of_isIntegral x).mem_nhds (by simp)

/- English proof (translation)
Introduce `k E Ω`. Use `intros`. Establish `hE : FiniteDimensional k E` using `Module.Finite.of_restrictScalars_finite ℚ k E`. Set `L : IntermediateField k Ω` to `(IsScalarTower.toAlgHom k E Ω).fieldRange`. Establish `hL : FiniteDimensional k L` using `LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv`.

Establish `hset : galOf k E Ω = L.fixingSubgroup`. Use extensionality with `σ`. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Use `show (∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x) ↔ _`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `h y ⟨x, rfl⟩`. Simplify using `using h x`. Introduce `h x`. Simplify using `using h _ ⟨x, rfl⟩`. Use `⟨⟨?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsTopologicalGroup.isInducing_iff_nhds_one]`. Use extensionality with `s`. Rewrite using `[Filter.mem_comap]`. Prove the components needed by the constructor for the conclusion. Introduce `hs`.

Take `⟨S, hS⟩` from `(mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mp hs`. Conclude with `⟨{σ : G k Ω | ∀ x ∈ S, σ x = x}, (mem_nhds_one_gal_iff_exists_finset_fixing k Ω _).mpr ⟨S, subset_rfl⟩, fun σ hσ => hS hσ⟩`. Introduce and unpack `⟨t, ht, hts⟩`. Take `⟨S, hS⟩` from `(mem_nhds_one_gal_iff_exists_finset_fixing k Ω t).mp ht`. Conclude with `(mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mpr ⟨S, fun σ hσ => hts (hS hσ)⟩`.

Introduce `σ τ h`. Use extensionality with `x`. Conclude with `DFunLike.congr_fun h x`. Rewrite using `[hset]`. Conclude with `L.fixingSubgroup_isOpen`.

Rewrite using `[hset, ← IntermediateField.finrank_eq_fixingSubgroup_index]`. Conclude with `(AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv.finrank_eq.symm`.
-/
theorem UpperTheory.V.Base.galEmbTop :
    ∀ (k E Ω : Type) [Field k] [NumberField k] [Field E] [NumberField E] [Field Ω] [Algebra k E] [Algebra k Ω] [Algebra E Ω]
      [IsScalarTower k E Ω] [IsAlgClosure k Ω] [IsAlgClosure E Ω],
      Topology.IsEmbedding (galEmb k E Ω) ∧ IsOpen (galOf k E Ω : Set (G k Ω)) ∧ (galOf k E Ω).index = Module.finrank k E := by
  intro k E Ω
  intros
  have hE : FiniteDimensional k E := Module.Finite.of_restrictScalars_finite ℚ k E
  let L : IntermediateField k Ω := (IsScalarTower.toAlgHom k E Ω).fieldRange
  have hL : FiniteDimensional k L :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv
  have hset : galOf k E Ω = L.fixingSubgroup := by
    ext σ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    show (∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x) ↔ _
    constructor
    · rintro h y ⟨x, rfl⟩
      simpa using h x
    · intro h x
      simpa using h _ ⟨x, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    ext s
    rw [Filter.mem_comap]
    constructor
    · intro hs
      obtain ⟨S, hS⟩ := (mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mp hs
      exact ⟨{σ : G k Ω | ∀ x ∈ S, σ x = x}, (mem_nhds_one_gal_iff_exists_finset_fixing k Ω _).mpr ⟨S, subset_rfl⟩,
        fun σ hσ => hS hσ⟩
    · rintro ⟨t, ht, hts⟩
      obtain ⟨S, hS⟩ := (mem_nhds_one_gal_iff_exists_finset_fixing k Ω t).mp ht
      exact (mem_nhds_one_gal_iff_exists_finset_fixing E Ω s).mpr ⟨S, fun σ hσ => hts (hS hσ)⟩
  · intro σ τ h
    ext x
    exact DFunLike.congr_fun h x
  · rw [hset]
    exact L.fixingSubgroup_isOpen
  · rw [hset, ← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom k E Ω)).toLinearEquiv.finrank_eq.symm
