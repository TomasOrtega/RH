import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.ValuationIntCastLtOneIff
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.MemRangeOfAevalRatEqZero

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Pointwise

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Use `letI : Algebra Ω (PadicAlgCl p) := ι.toAlgebra`. Use `letI : Algebra F (PadicAlgCl p) := (ι.comp (algebraMap F Ω)).toAlgebra`. Use `haveI : IsScalarTower F Ω (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : Normal F Ω := IsAlgClosure.normal F Ω`. Set `χ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p` to `AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun c => σ.commutes ⟨ι (algebraMap F Ω c), IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩⟩`.

Conclude with `⟨χ.restrictNormal Ω, fun x => χ.restrictNormal_commutes Ω x⟩`.
-/
theorem exists_res (ι : Ω →+* PadicAlgCl p) (σ : GK F ι) : ∃ τ : Ω ≃ₐ[F] Ω, ∀ x, ι (τ x) = σ (ι x) := by
  letI : Algebra Ω (PadicAlgCl p) := ι.toAlgebra
  letI : Algebra F (PadicAlgCl p) := (ι.comp (algebraMap F Ω)).toAlgebra
  haveI : IsScalarTower F Ω (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Normal F Ω := IsAlgClosure.normal F Ω
  let χ : PadicAlgCl p ≃ₐ[F] PadicAlgCl p := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun c =>
    σ.commutes ⟨ι (algebraMap F Ω c), IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩⟩
  exact ⟨χ.restrictNormal Ω, fun x => χ.restrictNormal_commutes Ω x⟩

def res (ι : Ω →+* PadicAlgCl p) : GK F ι →* (Ω ≃ₐ[F] Ω) where
  toFun σ := Classical.choose (exists_res ι σ)
  map_one' := by
    ext x
    apply ι.injective
    rw [Classical.choose_spec (exists_res ι 1) x]
    rfl
  map_mul' σ τ := by
    ext x
    apply ι.injective
    rw [Classical.choose_spec (exists_res ι (σ * τ)) x, AlgEquiv.mul_apply, AlgEquiv.mul_apply,
      Classical.choose_spec (exists_res ι σ), Classical.choose_spec (exists_res ι τ)]

/- English proof (translation)
The claim follows from `Classical.choose_spec (exists_res ι σ) x`.
-/
theorem res_spec (ι : Ω →+* PadicAlgCl p) (σ : GK F ι) (x : Ω) : ι (res ι σ x) = σ (ι x) :=
  Classical.choose_spec (exists_res ι σ) x

/- English proof (translation)
Rewrite using `[← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]`. Unfold `spectralNorm`. Conclude with `congrArg _ (minpoly.algEquiv_eq (σ.restrictScalars ℚ_[p]) y)`.
-/
private theorem norm_GK_lemma (ι : Ω →+* PadicAlgCl p) (σ : GK F ι) (y : PadicAlgCl p) : ‖σ y‖ = ‖y‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  unfold spectralNorm
  exact congrArg _ (minpoly.algEquiv_eq (σ.restrictScalars ℚ_[p]) y)

/- English proof (translation)
The claim follows from `(AddMonoidHomClass.isometry_of_norm σ (norm_GK_lemma ι σ)).continuous`.
-/
theorem continuous_GK (ι : Ω →+* PadicAlgCl p) (σ : GK F ι) : Continuous σ :=
  (AddMonoidHomClass.isometry_of_norm σ (norm_GK_lemma ι σ)).continuous

/- English proof (translation)
Introduce `σ τ h`. Establish `h2 : (σ : PadicAlgCl p → PadicAlgCl p) ∘ ι = (τ : PadicAlgCl p → PadicAlgCl p) ∘ ι`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply]`. Rewrite using `[← res_spec ι σ x, ← res_spec ι τ x, h]`.

Conclude with `AlgEquiv.ext (congrFun ((denseRange (F := F) ι).equalizer (continuous_GK ι σ) (continuous_GK ι τ) h2))`.
-/
theorem res_injective (ι : Ω →+* PadicAlgCl p) : Function.Injective (res (F := F) ι) := by
  intro σ τ h
  have h2 : (σ : PadicAlgCl p → PadicAlgCl p) ∘ ι = (τ : PadicAlgCl p → PadicAlgCl p) ∘ ι := by
    funext x
    simp only [Function.comp_apply]
    rw [← res_spec ι σ x, ← res_spec ι τ x, h]
  exact AlgEquiv.ext (congrFun
    ((denseRange (F := F) ι).equalizer (continuous_GK ι σ) (continuous_GK ι τ) h2))

/- English proof (translation)
Use `letI : Algebra Ω (PadicAlgCl p) := ι.toAlgebra`. Use `letI : Algebra F (PadicAlgCl p) := (ι.comp (algebraMap F Ω)).toAlgebra`. Use `haveI : IsScalarTower F Ω (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Set `φ : F →+* Kloc F ι` to `(ι.comp (algebraMap F Ω)).codRestrict (Kloc F ι) fun c => IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩`. Use `letI : Algebra F (Kloc F ι) := φ.toAlgebra`.

Use `haveI : IsScalarTower F (Kloc F ι) (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `hint : ∀ x : Ω, IsIntegral (Kloc F ι) (ι x)` using `fun x => ((Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral.map (IsScalarTower.toAlgHom F Ω (PadicAlgCl p))).tower_top`. Apply `continuous_of_continuousAt_one (res (F := F) ι)` to reduce the goal to its premises. Rewrite using `[ContinuousAt, map_one]`. Introduce `s hs`.

Take `⟨E, hEfin, hEs⟩` from `(krullTopology_mem_nhds_one_iff F Ω s).1 hs`. Use `haveI := hEfin`. Set `b` to `Module.finBasis F E`. Set `E' : IntermediateField (Kloc F ι) (PadicAlgCl p)` to `IntermediateField.adjoin (Kloc F ι) (Set.range fun i => ι (b i))`. Use `haveI : FiniteDimensional (Kloc F ι) E' := IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact hint _)`.

Establish `hE' : (E'.fixingSubgroup : Set (GK F ι)) ∈ nhds (1 : GK F ι)` using `(krullTopology_mem_nhds_one_iff (Kloc F ι) (PadicAlgCl p) _).2 ⟨E', inferInstance, le_rfl⟩`. Rewrite using `[Filter.mem_map]`. Use `Filter.mem_of_superset hE' fun σ hσ => hEs ?_` and prove the remaining obligations. Establish `hb : ∀ i, res ι σ (b i : Ω) = b i` using `fun i => by`. Apply `ι.injective` to reduce the goal to its premises.

Rewrite using `[res_spec]`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)`. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Establish `hL` using `b.ext (f₁ := (res ι σ).toLinearMap ∘ₗ E.val.toLinearMap) (f₂ := E.val.toLinearMap) fun i => hb i`.

Conclude with `LinearMap.congr_fun hL ⟨x, hx⟩`.
-/
theorem continuous_res (ι : Ω →+* PadicAlgCl p) : Continuous (res (F := F) ι) := by
  letI : Algebra Ω (PadicAlgCl p) := ι.toAlgebra
  letI : Algebra F (PadicAlgCl p) := (ι.comp (algebraMap F Ω)).toAlgebra
  haveI : IsScalarTower F Ω (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let φ : F →+* Kloc F ι := (ι.comp (algebraMap F Ω)).codRestrict (Kloc F ι)
    fun c => IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩
  letI : Algebra F (Kloc F ι) := φ.toAlgebra
  haveI : IsScalarTower F (Kloc F ι) (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hint : ∀ x : Ω, IsIntegral (Kloc F ι) (ι x) := fun x =>
    ((Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral.map
      (IsScalarTower.toAlgHom F Ω (PadicAlgCl p))).tower_top
  apply continuous_of_continuousAt_one (res (F := F) ι)
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨E, hEfin, hEs⟩ := (krullTopology_mem_nhds_one_iff F Ω s).1 hs
  haveI := hEfin
  let b := Module.finBasis F E
  let E' : IntermediateField (Kloc F ι) (PadicAlgCl p) :=
    IntermediateField.adjoin (Kloc F ι) (Set.range fun i => ι (b i))
  haveI : FiniteDimensional (Kloc F ι) E' :=
    IntermediateField.finiteDimensional_adjoin (by rintro _ ⟨i, rfl⟩; exact hint _)
  have hE' : (E'.fixingSubgroup : Set (GK F ι)) ∈ nhds (1 : GK F ι) :=
    (krullTopology_mem_nhds_one_iff (Kloc F ι) (PadicAlgCl p) _).2 ⟨E', inferInstance, le_rfl⟩
  rw [Filter.mem_map]
  refine Filter.mem_of_superset hE' fun σ hσ => hEs ?_
  have hb : ∀ i, res ι σ (b i : Ω) = b i := fun i => by
    apply ι.injective
    rw [res_spec]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hL := b.ext (f₁ := (res ι σ).toLinearMap ∘ₗ E.val.toLinearMap)
    (f₂ := E.val.toLinearMap) fun i => hb i
  exact LinearMap.congr_fun hL ⟨x, hx⟩

/- English proof (translation)
Establish `hτ : ∀ x, res ι σ x ∈ A ↔ x ∈ A` using `fun x => by rw [h, h, res_spec, norm_GK_lemma]`. Rewrite using `[Dec, ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨s, hs, rfl⟩`. Conclude with `(hτ s).2 hs`. Introduce `hx`. Use `⟨(res ι σ).symm x, (hτ _).1 ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AlgEquiv.apply_symm_apply]` and apply the resulting hypothesis.

Conclude with `AlgEquiv.apply_symm_apply _ _`.
-/
theorem res_mem_dec {A : ValuationSubring Ω} {ι : Ω →+* PadicAlgCl p} (h : Compat p A ι) (σ : GK F ι) :
    res ι σ ∈ Dec (F := F) A := by
  have hτ : ∀ x, res ι σ x ∈ A ↔ x ∈ A := fun x => by rw [h, h, res_spec, norm_GK_lemma]
  rw [Dec, ValuationSubring.decompositionSubgroup, MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (hτ s).2 hs
  · intro hx
    refine ⟨(res ι σ).symm x, (hτ _).1 ?_, ?_⟩
    · rwa [AlgEquiv.apply_symm_apply]
    · exact AlgEquiv.apply_symm_apply _ _

end ReciprocityTheory.Neutral.Cmp
