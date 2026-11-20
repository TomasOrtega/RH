import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessRelFnB
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimLeOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMorphismFactorizationStatement
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.NormCover

/- English proof (translation)
Use `M.ar.isIntegral` as an intermediate fact. Use `M.ar.isLocallyNoetherian` as an intermediate fact. Establish `: IsProper M.p` using `CommonModel.isProper_of_isProjOver M.ar.isProjOver`. Establish `: IsPreimmersion M.j` using `GlobalTheory.TrueGeo.SmallSec.isPreimmersion_j M`. Establish `: CharZero Y.Fn` using `charZero_of_injective_algebraMap (algebraMap F Y.Fn).injective`.

Establish `: CharZero K` using `charZero_of_injective_algebraMap (algebraMap Y.Fn K).injective`. Set `η` to `genericPoint Y.X`. Set `α : Y.X.presheaf.stalk η ⟶ CommRingCat.of K` to `CommRingCat.ofHom (algebraMap Y.Fn K)`. Set `g : Spec (.of K) ⟶ Y.X` to `Spec.map α ≫ Y.X.fromSpecStalk η`. Set `β : M.X.presheaf.stalk (M.j η) ⟶ CommRingCat.of K` to `M.j.stalkMap η ≫ α`.

Set `f : Spec (.of K) ⟶ M.X` to `Spec.map β ≫ M.X.fromSpecStalk (M.j η)`. Establish `hf : f = g ≫ M.j`. Simplify using `only [f, g, β, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]`. Establish `hfin : IsFinite f.fromNormalization`. Use `GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk M.p (M.j η) β ?_` and prove the remaining obligations.

Establish `h1 : (M.j.stalkMap η).hom.FiniteType` using `RingHom.FiniteType.of_surjective _ (M.j.stalkMap_surjective η)`. Establish `h2 : (algebraMap Y.Fn K).FiniteType` using `(RingHom.finite_algebraMap.2 inferInstance).finiteType`. Conclude with `(RingHom.FiniteType.comp h2 h1).essFiniteType`. Establish `hb` using `GlobalTheory.isPullback_normalizationMap_of_isLocalization (nonZeroDivisors (𝓞 F)) M.pb (GlobalTheory.isPullback_id_of_mono g M.j f hf)`. Establish `: IsFinite g.fromNormalization` using `MorphismProperty.of_isPullback hb hfin`.

Set `pt : Spec (.of K)` to `IsLocalRing.closedPoint (CommRingCat.of K)`. Establish `hgη : g pt = η`. Express the relevant statement in the definitionally equal form `Y.X.fromSpecStalk η (Spec.map α pt) = η`. Rewrite using `[show Spec.map α pt = IsLocalRing.closedPoint (Y.X.presheaf.stalk η) from Subsingleton.elim (α := PrimeSpectrum (Y.X.presheaf.stalk η)) _ _]`. Conclude with `Scheme.fromSpecStalk_closedPoint`.

Establish `hg0 : η ∈ Set.range g` using `⟨pt, hgη⟩`. Establish `: IsDominant g` using `⟨(dense_iff_closure_eq.2 (genericPoint_spec Y.X)).mono (Set.singleton_subset_iff.2 hg0)⟩`. Establish `hfη : f pt = M.j η`. Rewrite using `[hf]`. Express the relevant statement in the definitionally equal form `M.j (g pt) = M.j η`.

Rewrite using `[hgη]`. Establish `: IsDominant f`. Use `⟨?_⟩` and prove the remaining obligations. Establish `h0 : M.j η ∈ Set.range f` using `⟨pt, hfη⟩`. Establish `h1 : genericPoint M.X ∈ closure (Set.range f)` using `closure_mono (Set.singleton_subset_iff.2 h0) (specializes_iff_mem_closure.1 (GlobalTheory.TrueGeo.SmallSec.j_gen_specializes M) : genericPoint M.X ∈ closure ({M.j η} : Set M.X))`.

Establish `h2 : closure ({genericPoint M.X} : Set M.X) ⊆ closure (Set.range f)` using `closure_minimal (Set.singleton_subset_iff.2 h1) isClosed_closure`. Rewrite `h2` using `[show closure ({genericPoint M.X} : Set M.X) = Set.univ from genericPoint_spec M.X]`. Conclude with `dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset h2)`. Establish `: IsDominant g.fromNormalization`. Establish `: IsDominant (g.toNormalization ≫ g.fromNormalization)`.

Rewrite using `[Scheme.Hom.toNormalization_fromNormalization]`. Use `infer_instance`. Conclude with `IsDominant.of_comp g.toNormalization g.fromNormalization`. Establish `: IsDominant f.fromNormalization`. Establish `: IsDominant (f.toNormalization ≫ f.fromNormalization)`.

Rewrite using `[Scheme.Hom.toNormalization_fromNormalization]`. Use `infer_instance`. Conclude with `IsDominant.of_comp f.toNormalization f.fromNormalization`. Establish `: Surjective g.fromNormalization` using `surjective_of_isDominant_of_isClosed_range _ g.fromNormalization.isClosedMap.isClosed_range`. Establish `hρs : Surjective f.fromNormalization` using `surjective_of_isDominant_of_isClosed_range _ f.fromNormalization.isClosedMap.isClosed_range`.

Establish `hdim : topologicalKrullDim f.normalization = (Y.dim + 1 : ℕ)`. Rewrite using `[← M.ar.dim_eq]`. Use `le_antisymm (ProperCover.dim_le_of_residueDegree_pos f.fromNormalization (apply_genericPoint_of_isDominant f.fromNormalization) ?_) (PosBaseChange.dim_le_of_isClosedMap f.fromNormalization.isClosedMap hρs.surj)` and prove the remaining obligations. Set `` to `(f.fromNormalization.residueFieldMap (genericPoint f.normalization)).hom.toAlgebra`. Establish `: Module.Finite (M.X.residueField (f.fromNormalization (genericPoint f.normalization))) (f.normalization.residueField (genericPoint f.normalization))` using `residueFieldMap_finite_of_locallyQuasiFinite f.fromNormalization _`.

Conclude with `Module.finrank_pos`. Establish `hc : f ≫ M.p = (g ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F)`. Simplify using `only [hf, Category.assoc, M.pb.w]`. Establish `hfl : Flat (f.fromNormalization ≫ M.p)` using `GlobalTheory.flat_fromNormalization_comp f F M.p (g ≫ Y.str) hc`. Establish `hfZ : Flat (spMap (Int.castRingHom (𝓞 F)))`.

Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))`. Establish `: GlobalTheory.IsNormalScheme f.normalization` using `GlobalTheory.IsNormalScheme.normalization_of_isIntegral f`. Take `⟨hη, ψ, hψ⟩` from `GlobalTheory.T.generic_point_morphism_factorization Y.X K g rfl`. Set `V : Cover Y` to `{ X := f.normalization p := f.fromNormalization ≫ M.p ar := ⟨M.ar.isDomain, M.ar.finite, inferInstance, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin M.ar.isProjOver, inferInstance, hdim⟩ normal := GlobalTheory.IsNormalScheme.pred _ G := g.normalization j := GlobalTheory. …`.

Express the relevant statement in the definitionally equal form `_ = Spec.map (Y.X.presheaf.stalkSpecializes hη ≫ g.fromNormalization.stalkMap _) ≫ _`. Rewrite using `[Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk] }`. Conclude with `⟨V, f.fromNormalization, ψ, hb.w, hψ⟩`.
-/
theorem exists_cover (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (K : Type) [Field K]
    [Algebra Y.Fn K] [FiniteDimensional Y.Fn K] :
    ∃ (V : Cover Y) (ρ : V.X ⟶ M.X) (ψ : K →+* V.G.functionField),
      V.j ≫ ρ = V.π ≫ M.j ∧ ψ.comp (algebraMap Y.Fn K) = V.φ := by
  have := M.ar.isIntegral
  have := M.ar.isLocallyNoetherian
  have : IsProper M.p := CommonModel.isProper_of_isProjOver M.ar.isProjOver
  have : IsPreimmersion M.j := GlobalTheory.TrueGeo.SmallSec.isPreimmersion_j M
  have : CharZero Y.Fn := charZero_of_injective_algebraMap (algebraMap F Y.Fn).injective
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap Y.Fn K).injective
  let η := genericPoint Y.X
  let α : Y.X.presheaf.stalk η ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap Y.Fn K)
  let g : Spec (.of K) ⟶ Y.X := Spec.map α ≫ Y.X.fromSpecStalk η
  let β : M.X.presheaf.stalk (M.j η) ⟶ CommRingCat.of K := M.j.stalkMap η ≫ α
  let f : Spec (.of K) ⟶ M.X := Spec.map β ≫ M.X.fromSpecStalk (M.j η)
  have hf : f = g ≫ M.j := by
    simp only [f, g, β, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hfin : IsFinite f.fromNormalization := by
    refine GlobalTheory.isFinite_fromNormalization_SpecMap_fromSpecStalk M.p (M.j η) β ?_
    have h1 : (M.j.stalkMap η).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ (M.j.stalkMap_surjective η)
    have h2 : (algebraMap Y.Fn K).FiniteType := (RingHom.finite_algebraMap.2 inferInstance).finiteType
    exact (RingHom.FiniteType.comp h2 h1).essFiniteType
  have hb := GlobalTheory.isPullback_normalizationMap_of_isLocalization (nonZeroDivisors (𝓞 F)) M.pb
    (GlobalTheory.isPullback_id_of_mono g M.j f hf)
  have : IsFinite g.fromNormalization := MorphismProperty.of_isPullback hb hfin
  let pt : Spec (.of K) := IsLocalRing.closedPoint (CommRingCat.of K)
  have hgη : g pt = η := by
    change Y.X.fromSpecStalk η (Spec.map α pt) = η
    rw [show Spec.map α pt = IsLocalRing.closedPoint (Y.X.presheaf.stalk η) from
      Subsingleton.elim (α := PrimeSpectrum (Y.X.presheaf.stalk η)) _ _]
    exact Scheme.fromSpecStalk_closedPoint
  have hg0 : η ∈ Set.range g := ⟨pt, hgη⟩
  have : IsDominant g := ⟨(dense_iff_closure_eq.2 (genericPoint_spec Y.X)).mono
    (Set.singleton_subset_iff.2 hg0)⟩
  have hfη : f pt = M.j η := by
    rw [hf]
    change M.j (g pt) = M.j η
    rw [hgη]
  have : IsDominant f := by
    refine ⟨?_⟩
    have h0 : M.j η ∈ Set.range f := ⟨pt, hfη⟩
    have h1 : genericPoint M.X ∈ closure (Set.range f) :=
      closure_mono (Set.singleton_subset_iff.2 h0)
        (specializes_iff_mem_closure.1 (GlobalTheory.TrueGeo.SmallSec.j_gen_specializes M) :
          genericPoint M.X ∈ closure ({M.j η} : Set M.X))
    have h2 : closure ({genericPoint M.X} : Set M.X) ⊆ closure (Set.range f) :=
      closure_minimal (Set.singleton_subset_iff.2 h1) isClosed_closure
    rw [show closure ({genericPoint M.X} : Set M.X) = Set.univ from genericPoint_spec M.X] at h2
    exact dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset h2)
  have : IsDominant g.fromNormalization := by
    have : IsDominant (g.toNormalization ≫ g.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp g.toNormalization g.fromNormalization
  have : IsDominant f.fromNormalization := by
    have : IsDominant (f.toNormalization ≫ f.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp f.toNormalization f.fromNormalization
  have : Surjective g.fromNormalization :=
    surjective_of_isDominant_of_isClosed_range _ g.fromNormalization.isClosedMap.isClosed_range
  have hρs : Surjective f.fromNormalization :=
    surjective_of_isDominant_of_isClosed_range _ f.fromNormalization.isClosedMap.isClosed_range
  have hdim : topologicalKrullDim f.normalization = (Y.dim + 1 : ℕ) := by
    rw [← M.ar.dim_eq]
    refine le_antisymm (ProperCover.dim_le_of_residueDegree_pos f.fromNormalization
      (apply_genericPoint_of_isDominant f.fromNormalization) ?_)
      (PosBaseChange.dim_le_of_isClosedMap f.fromNormalization.isClosedMap hρs.surj)
    let := (f.fromNormalization.residueFieldMap (genericPoint f.normalization)).hom.toAlgebra
    have : Module.Finite (M.X.residueField (f.fromNormalization (genericPoint f.normalization)))
        (f.normalization.residueField (genericPoint f.normalization)) :=
      residueFieldMap_finite_of_locallyQuasiFinite f.fromNormalization _
    exact Module.finrank_pos
  have hc : f ≫ M.p = (g ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [hf, Category.assoc, M.pb.w]
  have hfl : Flat (f.fromNormalization ≫ M.p) := GlobalTheory.flat_fromNormalization_comp f F M.p (g ≫ Y.str) hc
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have : GlobalTheory.IsNormalScheme f.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral f
  obtain ⟨hη, ψ, hψ⟩ := GlobalTheory.T.generic_point_morphism_factorization Y.X K g rfl
  let V : Cover Y :=
    { X := f.normalization
      p := f.fromNormalization ≫ M.p
      ar := ⟨M.ar.isDomain, M.ar.finite, inferInstance,
        GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin M.ar.isProjOver, inferInstance, hdim⟩
      normal := GlobalTheory.IsNormalScheme.pred _
      G := g.normalization
      j := GlobalTheory.normalizationMap g f (𝟙 _) M.j (by simp [hf])
      π := g.fromNormalization
      pb := hb.paste_vert M.pb
      φ := SmallSec.fnMap g.fromNormalization hη
      φ_spec := by
        change _ = Spec.map (Y.X.presheaf.stalkSpecializes hη ≫ g.fromNormalization.stalkMap _) ≫ _
        rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
          Scheme.SpecMap_stalkMap_fromSpecStalk] }
  exact ⟨V, f.fromNormalization, ψ, hb.w, hψ⟩

end GlobalTheory.Mean4O.NormCover
