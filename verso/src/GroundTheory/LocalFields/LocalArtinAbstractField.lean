import Mathlib
import GroundTheory.LocalFields.LocalArtinTransport

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

section Embedding

variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]
  [IsSepClosure K Ω] in
/- English proof (translation)
The claim follows from `have := IsGalois.of_algEquiv ι.equivFieldRange { toIsMulCommutative := ⟨⟨fun σ τ => (AlgEquiv.autCongr ι.equivFieldRange).symm.injective ((map_mul _ σ τ).trans ((mul_comm' _ _).trans (map_mul _ τ σ).symm))⟩⟩ }`.
-/
theorem isAbelianGalois_fieldRange (ι : L →ₐ[K] Ω) : IsAbelianGalois K ι.fieldRange :=
  have := IsGalois.of_algEquiv ι.equivFieldRange
  { toIsMulCommutative := ⟨⟨fun σ τ => (AlgEquiv.autCongr ι.equivFieldRange).symm.injective
      ((map_mul _ σ τ).trans ((mul_comm' _ _).trans (map_mul _ τ σ).symm))⟩⟩ }

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsAbelianGalois K L]
  [IsSepClosure K Ω] in
/- English proof (translation)
The claim follows from `LinearEquiv.finiteDimensional ι.equivFieldRange.toLinearEquiv`.
-/
theorem finiteDimensional_fieldRange (ι : L →ₐ[K] Ω) : FiniteDimensional K ι.fieldRange :=
  LinearEquiv.finiteDimensional ι.equivFieldRange.toLinearEquiv

def artinOfEmbedding (ι : L →ₐ[K] Ω) : Kˣ →* (L ≃ₐ[K] L) :=
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  (AlgEquiv.autCongr ι.equivFieldRange).symm.toMonoidHom.comp
    ((restrictAb ι.fieldRange (le_maximalAbelianExtension _)).comp (localArtinMap K Ω))

/- English proof (translation)
Use `isAbelianGalois_fieldRange ι` as an intermediate fact. Use `finiteDimensional_fieldRange ι` as an intermediate fact. Establish `h : ι (artinOfEmbedding ι x z) = ((restrictAb ι.fieldRange (le_maximalAbelianExtension _) (localArtinMap K Ω x) (ι.equivFieldRange z) : ι.fieldRange) : Ω)`. Simplify using `only [artinOfEmbedding, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]`. Rewrite using `[← AlgHom.equivFieldRange_apply_coe, AlgEquiv.apply_symm_apply]`.

Both sides reduce to the same expression. Rewrite using `[h, restrictAb_apply]`. Both sides reduce to the same expression.
-/
theorem apply_artinOfEmbedding (ι : L →ₐ[K] Ω) (x : Kˣ) (z : L) :
    ι (artinOfEmbedding ι x z) =
      ((localArtinMap K Ω x ⟨ι z, (have := isAbelianGalois_fieldRange ι;
        le_maximalAbelianExtension ι.fieldRange) ⟨z, rfl⟩⟩ : maximalAbelianExtension K Ω) : Ω) := by
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  have h : ι (artinOfEmbedding ι x z) =
      ((restrictAb ι.fieldRange (le_maximalAbelianExtension _) (localArtinMap K Ω x)
        (ι.equivFieldRange z) : ι.fieldRange) : Ω) := by
    simp only [artinOfEmbedding, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      AlgEquiv.autCongr_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply]
    rw [← AlgHom.equivFieldRange_apply_coe, AlgEquiv.apply_symm_apply]
    rfl
  rw [h, restrictAb_apply]
  rfl

/- English proof (translation)
Establish `: Algebra.IsSeparable K Ω` using `IsSepClosure.separable`. Establish `: IsSepClosed Ω` using `IsSepClosure.sep_closed K`. Establish `: Algebra.IsSeparable ι₁.fieldRange Ω` using `Algebra.isSeparable_tower_top_of_isSeparable K ι₁.fieldRange Ω`. Take `⟨φ, hφ⟩` from `IsSepClosed.surjective_domRestrict_of_isSeparable (K := K) ι₁.fieldRange (M := Ω) (E := Ω) (ι₂.comp ι₁.equivFieldRange.symm.toAlgHom)`. Establish `hφι : ∀ z : L, φ (ι₁ z) = ι₂ z`.

Introduce `z`. Use `congrArg (fun f : ι₁.fieldRange →ₐ[K] Ω => f (ι₁.equivFieldRange z)) hφ` as an intermediate fact. Simplify using `only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at this`. Rewrite using `[← this]`. Both sides reduce to the same expression.

Use `set τ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)`. Use `set t := topologicalAbelianizationEquiv K Ω (τ : TopologicalAbelianization (Ω ≃ₐ[K] Ω))`. Establish `ht : ∀ w : maximalAbelianExtension K Ω, ((t w : maximalAbelianExtension K Ω) : Ω) = τ w` using `fun w => topologicalAbelianizationEquiv_mk_apply K Ω τ w`. Use extensionality with `x z`. Establish `key : ι₂ (artinOfEmbedding ι₁ x z) = ι₂ (artinOfEmbedding ι₂ x z)`.

Rewrite using `[← hφι (artinOfEmbedding ι₁ x z), apply_artinOfEmbedding ι₂]`. Express the relevant statement in the definitionally equal form `τ (ι₁ (artinOfEmbedding ι₁ x z)) = _`. Rewrite using `[apply_artinOfEmbedding ι₁]`. Use `set w : maximalAbelianExtension K Ω := ⟨ι₁ z, (have := isAbelianGalois_fieldRange ι₁; le_maximalAbelianExtension ι₁.fieldRange) ⟨z, rfl⟩⟩`. Establish `htw : t w = ⟨ι₂ z, (have` using `isAbelianGalois_fieldRange ι₂; le_maximalAbelianExtension ι₂.fieldRange) ⟨z, rfl⟩⟩ := Subtype.ext ((ht w).trans (hφι z))`.

Establish `hc : (localArtinMap K Ω x) (t w) = t ((localArtinMap K Ω x) w)`. Rewrite using `[← AlgEquiv.mul_apply, mul_comm' (localArtinMap K Ω x) t, AlgEquiv.mul_apply]`. Rewrite using `[← ht, ← hc, htw]`. Conclude with `ι₂.injective key`.
-/
theorem artinOfEmbedding_eq (ι₁ ι₂ : L →ₐ[K] Ω) : artinOfEmbedding ι₁ = artinOfEmbedding ι₂ := by
  have : Algebra.IsSeparable K Ω := IsSepClosure.separable
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : Algebra.IsSeparable ι₁.fieldRange Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K ι₁.fieldRange Ω
  obtain ⟨φ, hφ⟩ := IsSepClosed.surjective_domRestrict_of_isSeparable (K := K) ι₁.fieldRange
    (M := Ω) (E := Ω) (ι₂.comp ι₁.equivFieldRange.symm.toAlgHom)
  have hφι : ∀ z : L, φ (ι₁ z) = ι₂ z := by
    intro z
    have := congrArg (fun f : ι₁.fieldRange →ₐ[K] Ω => f (ι₁.equivFieldRange z)) hφ
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at this
    rw [← this]
    rfl
  set τ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
  set t := topologicalAbelianizationEquiv K Ω (τ : TopologicalAbelianization (Ω ≃ₐ[K] Ω))
  have ht : ∀ w : maximalAbelianExtension K Ω, ((t w : maximalAbelianExtension K Ω) : Ω) = τ w :=
    fun w => topologicalAbelianizationEquiv_mk_apply K Ω τ w
  ext x z
  have key : ι₂ (artinOfEmbedding ι₁ x z) = ι₂ (artinOfEmbedding ι₂ x z) := by
    rw [← hφι (artinOfEmbedding ι₁ x z), apply_artinOfEmbedding ι₂]
    change τ (ι₁ (artinOfEmbedding ι₁ x z)) = _
    rw [apply_artinOfEmbedding ι₁]
    set w : maximalAbelianExtension K Ω := ⟨ι₁ z, (have := isAbelianGalois_fieldRange ι₁;
      le_maximalAbelianExtension ι₁.fieldRange) ⟨z, rfl⟩⟩
    have htw : t w = ⟨ι₂ z, (have := isAbelianGalois_fieldRange ι₂;
        le_maximalAbelianExtension ι₂.fieldRange) ⟨z, rfl⟩⟩ :=
      Subtype.ext ((ht w).trans (hφι z))
    have hc : (localArtinMap K Ω x) (t w) = t ((localArtinMap K Ω x) w) := by
      rw [← AlgEquiv.mul_apply, mul_comm' (localArtinMap K Ω x) t, AlgEquiv.mul_apply]
    rw [← ht, ← hc, htw]
  exact ι₂.injective key

variable {Ω' : Type*} [Field Ω'] [Algebra K Ω'] [IsSepClosure K Ω']

/- English proof (translation)
Use extensionality with `x z`. Establish `key : ((ε : Ω →ₐ[K] Ω').comp ι) (artinOfEmbedding ((ε : Ω →ₐ[K] Ω').comp ι) x z) = ((ε : Ω →ₐ[K] Ω').comp ι) (artinOfEmbedding ι x z)`. Rewrite using `[apply_artinOfEmbedding]`. Express the relevant statement in the definitionally equal form `_ = ε (ι (artinOfEmbedding ι x z))`. Rewrite using `[apply_artinOfEmbedding, localArtinMap_algEquiv_apply]`.

Both sides reduce to the same expression. Conclude with `((ε : Ω →ₐ[K] Ω').comp ι).injective key`.
-/
theorem artinOfEmbedding_algEquiv_comp (ε : Ω ≃ₐ[K] Ω') (ι : L →ₐ[K] Ω) :
    artinOfEmbedding ((ε : Ω →ₐ[K] Ω').comp ι) = artinOfEmbedding ι := by
  ext x z
  have key : ((ε : Ω →ₐ[K] Ω').comp ι) (artinOfEmbedding ((ε : Ω →ₐ[K] Ω').comp ι) x z) =
      ((ε : Ω →ₐ[K] Ω').comp ι) (artinOfEmbedding ι x z) := by
    rw [apply_artinOfEmbedding]
    change _ = ε (ι (artinOfEmbedding ι x z))
    rw [apply_artinOfEmbedding, localArtinMap_algEquiv_apply]
    rfl
  exact ((ε : Ω →ₐ[K] Ω').comp ι).injective key

end Embedding

section Intrinsic

variable (K L) in

def localArtinMapOfField : Kˣ →* (L ≃ₐ[K] L) :=
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  artinOfEmbedding (IsSepClosed.lift : L →ₐ[K] SeparableClosure K)

/- English proof (translation)
Establish `: Algebra.IsSeparable K L` using `IsGalois.to_isSeparable`. Set `ε : SeparableClosure K ≃ₐ[K] Ω` to `IsSepClosure.equiv K (SeparableClosure K) Ω`. Rewrite using `[localArtinMapOfField, ← artinOfEmbedding_algEquiv_comp ε]`. Conclude with `artinOfEmbedding_eq _ _`.
-/
theorem localArtinMapOfField_eq_artinOfEmbedding {Ω : Type*} [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (ι : L →ₐ[K] Ω) : localArtinMapOfField K L = artinOfEmbedding ι := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  let ε : SeparableClosure K ≃ₐ[K] Ω := IsSepClosure.equiv K (SeparableClosure K) Ω
  rw [localArtinMapOfField, ← artinOfEmbedding_algEquiv_comp ε]
  exact artinOfEmbedding_eq _ _

/- English proof (translation)
Use `isAbelianGalois_fieldRange ι` as an intermediate fact. Use `finiteDimensional_fieldRange ι` as an intermediate fact. Establish `hker : (artinOfEmbedding ι).ker = ((restrictAb ι.fieldRange (le_maximalAbelianExtension _)).comp (localArtinMap K Ω)).ker`. Use extensionality with `x`. Simplify using `[artinOfEmbedding, MonoidHom.mem_ker]`.

Rewrite using `[hker, ker_restrictAb_localArtinMap]`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩`. Use `⟨Units.map ι.equivFieldRange.symm.toRingEquiv.toRingHom.toMonoidHom w, Units.ext ?_⟩` and prove the remaining obligations.

Simplify using `[coe_normUnits, Algebra.norm_eq_of_algEquiv]`. Introduce and unpack `⟨w, rfl⟩`. Use `⟨Units.map ι.equivFieldRange.toRingEquiv.toRingHom.toMonoidHom w, Units.ext ?_⟩` and prove the remaining obligations. Simplify using `[coe_normUnits, Algebra.norm_eq_of_algEquiv]`.
-/
theorem ker_artinOfEmbedding {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (ι : L →ₐ[K] Ω) : (artinOfEmbedding ι).ker = (normUnits K L).range := by
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  have hker : (artinOfEmbedding ι).ker =
      ((restrictAb ι.fieldRange (le_maximalAbelianExtension _)).comp (localArtinMap K Ω)).ker := by
    ext x
    simp [artinOfEmbedding, MonoidHom.mem_ker]
  rw [hker, ker_restrictAb_localArtinMap]
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨Units.map ι.equivFieldRange.symm.toRingEquiv.toRingHom.toMonoidHom w, Units.ext ?_⟩
    simp [coe_normUnits, Algebra.norm_eq_of_algEquiv]
  · rintro ⟨w, rfl⟩
    refine ⟨Units.map ι.equivFieldRange.toRingEquiv.toRingHom.toMonoidHom w, Units.ext ?_⟩
    simp [coe_normUnits, Algebra.norm_eq_of_algEquiv]

/- English proof (translation)
Establish `: Algebra.IsSeparable K L` using `IsGalois.to_isSeparable`. Conclude with `ker_artinOfEmbedding _`.
-/
theorem ker_localArtinMapOfField : (localArtinMapOfField K L).ker = (normUnits K L).range := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  exact ker_artinOfEmbedding _

/- English proof (translation)
Establish `: Algebra.IsSeparable K L` using `IsGalois.to_isSeparable`. Use `set ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift`. Use `isAbelianGalois_fieldRange ι` as an intermediate fact. Use `finiteDimensional_fieldRange ι` as an intermediate fact. Introduce `σ`.

Take `⟨x, hx⟩` from `surjective_restrictAb_localArtinMap (Ω := SeparableClosure K) ι.fieldRange (AlgEquiv.autCongr ι.equivFieldRange σ)`. Use `⟨x, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(AlgEquiv.autCongr ι.equivFieldRange).symm _ = σ`. Rewrite using `[hx, MulEquiv.symm_apply_apply]`.
-/
theorem surjective_localArtinMapOfField : Function.Surjective (localArtinMapOfField K L) := by
  have : Algebra.IsSeparable K L := IsGalois.to_isSeparable
  set ι : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  have := isAbelianGalois_fieldRange ι
  have := finiteDimensional_fieldRange ι
  intro σ
  obtain ⟨x, hx⟩ := surjective_restrictAb_localArtinMap (Ω := SeparableClosure K) ι.fieldRange
    (AlgEquiv.autCongr ι.equivFieldRange σ)
  refine ⟨x, ?_⟩
  change (AlgEquiv.autCongr ι.equivFieldRange).symm _ = σ
  rw [hx, MulEquiv.symm_apply_apply]

def localReciprocityOfField : Kˣ ⧸ (normUnits K L).range ≃* (L ≃ₐ[K] L) :=
  (QuotientGroup.quotientMulEquivOfEq ker_localArtinMapOfField.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ surjective_localArtinMapOfField)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem localReciprocityOfField_mk (x : Kˣ) :
    localReciprocityOfField (K := K) (L := L) (x : Kˣ ⧸ (normUnits K L).range) =
      localArtinMapOfField K L x :=
  rfl

end Intrinsic

end GroundTheory.LocalField
