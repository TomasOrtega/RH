import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.ArthurClozel
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmSubfieldsCompositumClosedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDecompositionGroupsCoverOpenQuotientStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.KLift

/- English proof (translation)
Take `⟨E', hE', hsub⟩` from `(krullTopology_mem_nhds_one_iff L Ω _).1 (hN.mem_nhds N.one_mem)`. Use `haveI : FiniteDimensional K E' := Module.Finite.trans L E'`. Use `haveI : FiniteDimensional K (E'.restrictScalars K) := this`. Use `Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen (E'.restrictScalars K))` and prove the remaining obligations. Introduce `g hg`.

Establish `hfix : ∀ x ∈ E', g x = x` using `fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg x hx`. Set `g' : Ω ≃ₐ[L] Ω` to `{ g.toRingEquiv with commutes' := fun l => hfix _ (E'.algebraMap_mem l) }`. Use `⟨g', hsub ?_, ?_⟩` and prove the remaining obligations. Conclude with `(IntermediateField.mem_fixingSubgroup_iff E' g').2 hfix`. Use extensionality with `x`.

Both sides reduce to the same expression.
-/
theorem isOpen_map_restrictScalars {K L Ω : Type} [Field K] [Field L] [Field Ω] [Algebra K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [FiniteDimensional K L]
    (N : Subgroup (Ω ≃ₐ[L] Ω)) (hN : IsOpen (N : Set (Ω ≃ₐ[L] Ω))) :
    IsOpen ((N.map (AlgEquiv.restrictScalarsHom K)) : Set (Ω ≃ₐ[K] Ω)) := by
  obtain ⟨E', hE', hsub⟩ := (krullTopology_mem_nhds_one_iff L Ω _).1 (hN.mem_nhds N.one_mem)
  haveI : FiniteDimensional K E' := Module.Finite.trans L E'
  haveI : FiniteDimensional K (E'.restrictScalars K) := this
  refine Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen (E'.restrictScalars K))
  intro g hg
  have hfix : ∀ x ∈ E', g x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg x hx
  let g' : Ω ≃ₐ[L] Ω := { g.toRingEquiv with commutes' := fun l => hfix _ (E'.algebraMap_mem l) }
  refine ⟨g', hsub ?_, ?_⟩
  · exact (IntermediateField.mem_fixingSubgroup_iff E' g').2 hfix
  · ext x; rfl

end GlobalTheory.KLift

open GlobalTheory.KLift in

/- English proof (translation)
Introduce `Ω _ E _ _ _ _ _ v N hN`. Use `haveI hFE : Algebra.IsAlgebraic (maximalRealSubfield E) E := Algebra.IsAlgebraic.of_finite _ _`. Use `haveI : Algebra.IsAlgebraic (maximalRealSubfield E) Ω := Algebra.IsAlgebraic.trans (maximalRealSubfield E) E Ω`. Use `haveI hcF : IsAlgClosure (maximalRealSubfield E) Ω := ⟨IsAlgClosure.isAlgClosed E, inferInstance⟩`. Take `⟨T, hvT, hT⟩` from `GlobalTheory.T.finite_decompositionGroups_cover_openQuotient Ω (maximalRealSubfield E) v (N.map (AlgEquiv.restrictScalarsHom (maximalRealSubfield E))) (isOpen_map_restrictScalars N hN)`.

Use `⟨T, hvT, ?_⟩` and prove the remaining obligations. Introduce `F₁ hfd hgal hsolv hreal hdec`. Establish `hre : ∀ z ∈ F₁, ∀ φ : Ω →+* ℂ, star (φ z) = φ z`. Introduce `z hz φ`. Establish `h` using `ComplexEmbedding.isReal_iff.1 (hreal (φ.comp F₁.val.toRingHom))`.

Use `RingHom.congr_fun h ⟨z, hz⟩` as an intermediate fact. Rewrite `this` using `[ComplexEmbedding.conjugate_coe_eq]`. Simplify using `using this`. Set `M : IntermediateField E Ω` to `IntermediateField.adjoin E (F₁ : Set Ω)`. Establish `hF₁M : ∀ z ∈ F₁, z ∈ M` using `fun z hz => IntermediateField.subset_adjoin E _ hz`.

Establish `hfix : ∀ g : G E Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ↔ ∀ z ∈ F₁, g z = z`. Introduce `g`. Prove the components needed by the constructor for the conclusion. Introduce `h z hz`. Conclude with `h ⟨z, hF₁M z hz⟩`.

Introduce `h x`. Establish `hle : M ≤ IntermediateField.fixedField (Subgroup.zpowers g)`. Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations. Introduce `z hz`. Rewrite using `[SetLike.mem_coe, IntermediateField.mem_fixedField_iff]`.

Introduce `f hf`. Take `⟨k, rfl⟩` from `Subgroup.mem_zpowers_iff.1 hf`. Conclude with `(MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := g)).2 (h z hz) k`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 (hle x.2) g (Subgroup.mem_zpowers g)`. Use `haveI : Normal (maximalRealSubfield E) F₁ := hgal.to_normal`.

Use `haveI : Normal E Ω := IsAlgClosure.normal E Ω`. Use `haveI : Normal (maximalRealSubfield E) Ω := IsAlgClosure.normal _ Ω`. Establish `hmap : ∀ σ : Ω →ₐ[E] Ω, ∀ z ∈ F₁, σ z ∈ F₁`. Introduce `σ z hz`. Conclude with `IntermediateField.normal_iff_forall_map_le.1 inferInstance (σ.restrictScalars (maximalRealSubfield E)) ((IntermediateField.mem_map _).2 ⟨z, hz, rfl⟩)`.

Use `haveI hMn : Normal E M := by`. Use `IntermediateField.normal_iff_forall_map_le.2 fun σ => ?_` and prove the remaining obligations. Use `show (IntermediateField.adjoin E (F₁ : Set Ω)).map σ ≤ IntermediateField.adjoin E (F₁ : Set Ω)`. Rewrite using `[IntermediateField.adjoin_map]`. Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨z, hz, rfl⟩`. Conclude with `hF₁M _ (hmap σ z hz)`. Use `haveI hMfd : FiniteDimensional E M := by`. Set `b` to `Module.finBasis (maximalRealSubfield E) F₁`. Set `S : Set Ω` to `Set.range (fun i => ((b i : F₁) : Ω))`.

Use `haveI : Finite S := (Set.finite_range _).to_subtype`. Establish `hint : ∀ x ∈ S, IsIntegral E x` using `fun x _ => Algebra.IsIntegral.isIntegral x`. Use `haveI := IntermediateField.finiteDimensional_adjoin hint`. Establish `hle : M ≤ IntermediateField.adjoin E S`. Use `IntermediateField.adjoin_le_iff.2 ?_` and prove the remaining obligations.

Introduce `z hz`. Establish `hsum` using `b.sum_repr ⟨z, hz⟩`. Establish `h2` using `congrArg (fun y : F₁ => (y : Ω)) hsum`. Simplify using `only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h2`. Establish `: z = ∑ i, algebraMap E Ω ((b.repr ⟨z, hz⟩ i : maximalRealSubfield E) : E) * ((b i : F₁) : Ω)`.

Use `h2.symm.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E Ω]`. Both sides reduce to the same expression. Rewrite using `[SetLike.mem_coe, this]`. Conclude with `sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.subset_adjoin E S ⟨i, rfl⟩)`.

Conclude with `FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap (IntermediateField.inclusion hle).toRingHom.injective`. Use `haveI : NumberField M := NumberField.of_module_finite E M`. Use `haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) _⟩`. Use `haveI : IsGalois E M := ⟨⟩`. Establish `hCM : IsCMField M` using `(GlobalTheory.T.cm_subfields_compositum_closed Ω E).2.2 M (F₁ : Set Ω) (fun x hx φ => by`.

Use `hre x hx φ` as an intermediate fact. Rewrite `this` using `[Complex.star_def]`. Conclude with `Complex.conj_eq_iff_im.1 this) rfl`. Use `haveI : Group.IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) := hsolv`. Establish `hsolvM : IsSolvable (M ≃ₐ[E] M)`.

Set `ψ : (Ω ≃ₐ[E] Ω) →* (M ≃ₐ[E] M)` to `AlgEquiv.restrictNormalHom M`. Set `φ : (Ω ≃ₐ[E] Ω) →* (F₁ ≃ₐ[maximalRealSubfield E] F₁)` to `(AlgEquiv.restrictNormalHom F₁).comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E))`. Establish `hψ : Function.Surjective ψ` using `AlgEquiv.restrictNormalHom_surjective Ω`. Establish `hker : ψ.ker = φ.ker`. Use extensionality with `g`.

Rewrite using `[MonoidHom.mem_ker, MonoidHom.mem_ker]`. Establish `e1 : ψ g = 1 ↔ ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x`. Simplify using `only [AlgEquiv.ext_iff, AlgEquiv.one_apply]`. Use `forall_congr' fun x => ?_` and prove the remaining obligations. Rewrite using `[← (algebraMap M Ω).injective.eq_iff]`.

Use `show algebraMap M Ω (AlgEquiv.restrictNormal g M x) = _ ↔ _`. Rewrite using `[AlgEquiv.restrictNormal_commutes]`. Establish `e2 : φ g = 1 ↔ ∀ z ∈ F₁, g z = z`. Simplify using `only [AlgEquiv.ext_iff, AlgEquiv.one_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce `h z hz`. Use `congrArg (algebraMap F₁ Ω) (h ⟨z, hz⟩)` as an intermediate fact. Rewrite `this` using `[show φ g ⟨z, hz⟩ = AlgEquiv.restrictNormal (AlgEquiv.restrictScalarsHom _ g) F₁ ⟨z, hz⟩ from rfl, AlgEquiv.restrictNormal_commutes]`. Conclude with `this`. Introduce `h y`.

Apply `(algebraMap F₁ Ω).injective` to reduce the goal to its premises. Use `show algebraMap F₁ Ω (AlgEquiv.restrictNormal (AlgEquiv.restrictScalarsHom _ g) F₁ y) = _`. Rewrite using `[AlgEquiv.restrictNormal_commutes]`. Conclude with `h y y.2`. Rewrite using `[e1, e2, hfix]`.

Set `ρ : (M ≃ₐ[E] M) →* (F₁ ≃ₐ[maximalRealSubfield E] F₁)` to `(QuotientGroup.kerLift φ).comp ((QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom.comp (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom)`. Establish `hinj : Function.Injective ρ` using `(QuotientGroup.kerLift_injective φ).comp ((QuotientGroup.quotientMulEquivOfEq hker).injective.comp (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.injective)`. Conclude with `solvable_of_solvable_injective hinj`. Use `⟨M, inferInstance, inferInstance, hCM, inferInstance, inferInstance, inferInstance, inferInstance, ⟨inferInstance, hsolvM, ?_⟩, hfix, ?_⟩` and prove the remaining obligations. Introduce `g`.

Take `⟨u, hu, A', hA', x, hx, n', hn', hgx⟩` from `hT (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g)`. Take `⟨n, hn, rfl⟩` from `Subgroup.mem_map.1 hn'`. Establish `hxF : ∀ z ∈ F₁, x z = z` using `fun z hz => (IntermediateField.mem_fixingSubgroup_iff F₁ x).1 (hdec u hu A' hA' hx) z hz`. Establish `hyx : AlgEquiv.restrictScalarsHom (maximalRealSubfield E) (g * n⁻¹) = x`. Rewrite using `[map_mul, map_inv, hgx, mul_inv_cancel_right]`.

Establish `hyM : ∀ m : M, (g * n⁻¹) (algebraMap M Ω m) = algebraMap M Ω m` using `(hfix (g * n⁻¹)).2 fun z hz => (DFunLike.congr_fun hyx z).trans (hxF z hz)`. Use `⟨{ (g * n⁻¹) with commutes' := hyM }, n, hn, ?_⟩` and prove the remaining obligations. Use extensionality with `w`. Use `show g w = (g * n⁻¹) (n w)`. Simplify using the standard rewrite rules.

Introduce `z hz`. Use `⟨⟨z, hF₁M z hz⟩, ?_, rfl⟩` and prove the remaining obligations. Introduce `φ`. Use `letI : Algebra M ℂ := φ.toAlgebra`. Set `ψ : Ω →ₐ[M] ℂ` to `IsAlgClosed.lift`.

Establish `h1 : φ ⟨z, hF₁M z hz⟩ = ψ z` using `(ψ.commutes ⟨z, hF₁M z hz⟩).symm`. Rewrite using `[h1]`. Conclude with `hre z hz ψ.toRingHom`.
-/
theorem GlobalTheory.KLift.exists_cm_lift : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), v ∉ T ∧ ∀ F₁ : IntermediateField (maximalRealSubfield E) Ω, FiniteDimensional (maximalRealSubfield E) F₁ → IsGalois (maximalRealSubfield E) F₁ → IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) → (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) → (∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := maximalRealSubfield E) A' ≤ F₁.fixingSubgroup) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g : G E Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ↔ ∀ z ∈ F₁, g z = z) ∧ ∀ z ∈ F₁, ∃ x ∈ maximalRealSubfield M, algebraMap M Ω x = z := by
  intro Ω _ E _ _ _ _ _ v N hN
  classical
  haveI hFE : Algebra.IsAlgebraic (maximalRealSubfield E) E := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (maximalRealSubfield E) Ω :=
    Algebra.IsAlgebraic.trans (maximalRealSubfield E) E Ω
  haveI hcF : IsAlgClosure (maximalRealSubfield E) Ω := ⟨IsAlgClosure.isAlgClosed E, inferInstance⟩
  obtain ⟨T, hvT, hT⟩ := GlobalTheory.T.finite_decompositionGroups_cover_openQuotient Ω (maximalRealSubfield E) v
    (N.map (AlgEquiv.restrictScalarsHom (maximalRealSubfield E))) (isOpen_map_restrictScalars N hN)
  refine ⟨T, hvT, ?_⟩
  intro F₁ hfd hgal hsolv hreal hdec
  have hre : ∀ z ∈ F₁, ∀ φ : Ω →+* ℂ, star (φ z) = φ z := by
    intro z hz φ
    have h := ComplexEmbedding.isReal_iff.1 (hreal (φ.comp F₁.val.toRingHom))
    have := RingHom.congr_fun h ⟨z, hz⟩
    rw [ComplexEmbedding.conjugate_coe_eq] at this
    simpa using this
  let M : IntermediateField E Ω := IntermediateField.adjoin E (F₁ : Set Ω)
  have hF₁M : ∀ z ∈ F₁, z ∈ M := fun z hz => IntermediateField.subset_adjoin E _ hz
  have hfix : ∀ g : G E Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ↔ ∀ z ∈ F₁, g z = z := by
    intro g
    constructor
    · intro h z hz; exact h ⟨z, hF₁M z hz⟩
    · intro h x
      have hle : M ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
        refine IntermediateField.adjoin_le_iff.2 ?_
        intro z hz
        rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
        intro f hf
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
        exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := g)).2 (h z hz) k
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle x.2) g (Subgroup.mem_zpowers g)
  haveI : Normal (maximalRealSubfield E) F₁ := hgal.to_normal
  haveI : Normal E Ω := IsAlgClosure.normal E Ω
  haveI : Normal (maximalRealSubfield E) Ω := IsAlgClosure.normal _ Ω
  have hmap : ∀ σ : Ω →ₐ[E] Ω, ∀ z ∈ F₁, σ z ∈ F₁ := by
    intro σ z hz
    exact IntermediateField.normal_iff_forall_map_le.1 inferInstance
      (σ.restrictScalars (maximalRealSubfield E)) ((IntermediateField.mem_map _).2 ⟨z, hz, rfl⟩)
  haveI hMn : Normal E M := by
    refine IntermediateField.normal_iff_forall_map_le.2 fun σ => ?_
    show (IntermediateField.adjoin E (F₁ : Set Ω)).map σ ≤ IntermediateField.adjoin E (F₁ : Set Ω)
    rw [IntermediateField.adjoin_map]
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hF₁M _ (hmap σ z hz)
  haveI hMfd : FiniteDimensional E M := by
    let b := Module.finBasis (maximalRealSubfield E) F₁
    let S : Set Ω := Set.range (fun i => ((b i : F₁) : Ω))
    haveI : Finite S := (Set.finite_range _).to_subtype
    have hint : ∀ x ∈ S, IsIntegral E x := fun x _ => Algebra.IsIntegral.isIntegral x
    haveI := IntermediateField.finiteDimensional_adjoin hint
    have hle : M ≤ IntermediateField.adjoin E S := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      intro z hz
      have hsum := b.sum_repr ⟨z, hz⟩
      have h2 := congrArg (fun y : F₁ => (y : Ω)) hsum
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h2
      have : z = ∑ i, algebraMap E Ω ((b.repr ⟨z, hz⟩ i : maximalRealSubfield E) : E) * ((b i : F₁) : Ω) := by
        refine h2.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E Ω]
        rfl
      rw [SetLike.mem_coe, this]
      exact sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.subset_adjoin E S ⟨i, rfl⟩)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).toRingHom.injective
  haveI : NumberField M := NumberField.of_module_finite E M
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  haveI : IsGalois E M := ⟨⟩
  have hCM : IsCMField M := (GlobalTheory.T.cm_subfields_compositum_closed Ω E).2.2 M (F₁ : Set Ω) (fun x hx φ => by
      have := hre x hx φ
      rw [Complex.star_def] at this
      exact Complex.conj_eq_iff_im.1 this) rfl
  haveI : Group.IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) := hsolv
  have hsolvM : IsSolvable (M ≃ₐ[E] M) := by
    let ψ : (Ω ≃ₐ[E] Ω) →* (M ≃ₐ[E] M) := AlgEquiv.restrictNormalHom M
    let φ : (Ω ≃ₐ[E] Ω) →* (F₁ ≃ₐ[maximalRealSubfield E] F₁) :=
      (AlgEquiv.restrictNormalHom F₁).comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E))
    have hψ : Function.Surjective ψ := AlgEquiv.restrictNormalHom_surjective Ω
    have hker : ψ.ker = φ.ker := by
      ext g
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      have e1 : ψ g = 1 ↔ ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x := by
        simp only [AlgEquiv.ext_iff, AlgEquiv.one_apply]
        refine forall_congr' fun x => ?_
        rw [← (algebraMap M Ω).injective.eq_iff]
        show algebraMap M Ω (AlgEquiv.restrictNormal g M x) = _ ↔ _
        rw [AlgEquiv.restrictNormal_commutes]
      have e2 : φ g = 1 ↔ ∀ z ∈ F₁, g z = z := by
        simp only [AlgEquiv.ext_iff, AlgEquiv.one_apply]
        constructor
        · intro h z hz
          have := congrArg (algebraMap F₁ Ω) (h ⟨z, hz⟩)
          rw [show φ g ⟨z, hz⟩ = AlgEquiv.restrictNormal (AlgEquiv.restrictScalarsHom _ g) F₁ ⟨z, hz⟩
            from rfl, AlgEquiv.restrictNormal_commutes] at this
          exact this
        · intro h y
          apply (algebraMap F₁ Ω).injective
          show algebraMap F₁ Ω (AlgEquiv.restrictNormal (AlgEquiv.restrictScalarsHom _ g) F₁ y) = _
          rw [AlgEquiv.restrictNormal_commutes]
          exact h y y.2
      rw [e1, e2, hfix]
    let ρ : (M ≃ₐ[E] M) →* (F₁ ≃ₐ[maximalRealSubfield E] F₁) :=
      (QuotientGroup.kerLift φ).comp ((QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom.comp
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom)
    have hinj : Function.Injective ρ :=
      (QuotientGroup.kerLift_injective φ).comp ((QuotientGroup.quotientMulEquivOfEq hker).injective.comp
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.injective)
    exact solvable_of_solvable_injective hinj
  refine ⟨M, inferInstance, inferInstance, hCM, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨inferInstance, hsolvM, ?_⟩, hfix, ?_⟩
  · intro g
    obtain ⟨u, hu, A', hA', x, hx, n', hn', hgx⟩ :=
      hT (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g)
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hn'
    have hxF : ∀ z ∈ F₁, x z = z := fun z hz =>
      (IntermediateField.mem_fixingSubgroup_iff F₁ x).1 (hdec u hu A' hA' hx) z hz
    have hyx : AlgEquiv.restrictScalarsHom (maximalRealSubfield E) (g * n⁻¹) = x := by
      rw [map_mul, map_inv, hgx, mul_inv_cancel_right]
    have hyM : ∀ m : M, (g * n⁻¹) (algebraMap M Ω m) = algebraMap M Ω m :=
      (hfix (g * n⁻¹)).2 fun z hz => (DFunLike.congr_fun hyx z).trans (hxF z hz)
    refine ⟨{ (g * n⁻¹) with commutes' := hyM }, n, hn, ?_⟩
    ext w
    show g w = (g * n⁻¹) (n w)
    simp
  · intro z hz
    refine ⟨⟨z, hF₁M z hz⟩, ?_, rfl⟩
    intro φ
    letI : Algebra M ℂ := φ.toAlgebra
    let ψ : Ω →ₐ[M] ℂ := IsAlgClosed.lift
    have h1 : φ ⟨z, hF₁M z hz⟩ = ψ z := (ψ.commutes ⟨z, hF₁M z hz⟩).symm
    rw [h1]
    exact hre z hz ψ.toRingHom
