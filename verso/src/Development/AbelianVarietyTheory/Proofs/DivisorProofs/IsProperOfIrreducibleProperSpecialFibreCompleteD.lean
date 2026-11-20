import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowLemmaProjectiveModification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageClosureCompleteDVRSpecialFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOfClosedCoverInUniversallyCloseStatement
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.FibreProper

/- English proof (translation)
Introduce `O _ _ _ _ X f hirr hsep hlft hqc hx hfib`. Take `⟨x₀, hx₀⟩` from `hx`. Establish `hne : Nonempty X` using `⟨x₀⟩`. Take `⟨Y, P, π, q, s, U, hπ, hUne, hiso, hproj, hq, hcomm⟩` from `GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver O X f hsep hlft hqc hne`. Establish `hs : IsProper s`.

Take `⟨N, i, hi, rfl⟩` from `hproj`. Use `ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N` as an intermediate fact. Use `infer_instance`. Use `set C : Set Y := π ⁻¹' (U : Set X) with hC`. Establish `hsurj : Function.Surjective (π ∣_ U)` using `fun y => ⟨(inv (π ∣_ U)) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩`.

Establish `hUsub : (U : Set X) ⊆ π '' C`. Introduce `u hu`. Take `⟨v, hv⟩` from `hsurj ⟨u, hu⟩`. Use `⟨v.1, v.2, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hv` as an intermediate fact.

Rewrite `this` using `[morphismRestrict_base_coe]`. Then use the resulting hypothesis. Establish `hUirr : IsIrreducible (U : Set X)` using `⟨hUne, (IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset U.isOpen (Set.subset_univ _)⟩`. Establish `hCirr : IsIrreducible C` using `by haveI : IrreducibleSpace (U : Set X) := Subtype.irreducibleSpace hUirr haveI : IrreducibleSpace (π ⁻¹ᵁ U).toScheme := (Scheme.homeoOfIso (asIso (π ∣_ U))).irreducibleSpace_iff.2 (inferInstanceAs (IrreducibleSpace (U : Set X)))`. Establish `h` using `(IrreducibleSpace.isIrreducible_univ (π ⁻¹ᵁ U).toScheme).image (fun y => (π ⁻¹ᵁ U).ι y) ((π ⁻¹ᵁ U).ι.continuous.continuousOn)`. Use `h using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Conclude with `⟨⟨y, hy⟩, Set.mem_univ _, rfl⟩`. Introduce and unpack `⟨v, -, rfl⟩`.

Conclude with `v.2`. Establish `hπT : π '' closure C = Set.univ`. Establish `hcl : IsClosed (π '' closure C)` using `π.isClosedMap _ isClosed_closure`. Establish `hd : Dense (U : Set X)` using `U.isOpen.dense hUne`. Use `Set.eq_univ_of_univ_subset ?_` and prove the remaining obligations.

Rewrite using `[← hd.closure_eq]`. Conclude with `closure_minimal (hUsub.trans (Set.image_mono subset_closure)) hcl`. Establish `hmeet : ∃ y ∈ closure C, (q ≫ s) y = IsLocalRing.closedPoint O`. Take `⟨y, hy, hyx⟩ : x₀ ∈ π '' closure C` from `hπT ▸ Set.mem_univ x₀`. Use `⟨y, hy, ?_⟩` and prove the remaining obligations.

Rewrite using `[hcomm, Scheme.Hom.comp_apply, hyx, hx₀]`. Establish `hfib' : IsProper (pullback.snd (q ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))))`. Rewrite using `[hcomm, (Iso.eq_inv_comp (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) π)).2 (pullbackRightPullbackFstIso_hom_snd (f := f) (g := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) (f' := π))]`. Use `infer_instance`. Establish `hclosed` using `GlobalTheory.T.isClosed_image_closure_completeDVR_specialFibre O Y P q s C hs hq hfib' hCirr hmeet`.

Establish `huc : UniversallyClosed f` using `GlobalTheory.T.universallyClosed_of_closed_image_cover _ X Y P f π q s (closure C) inferInstance hq hcomm isClosed_closure hclosed hπT`. Conclude with `⟨⟩`.
-/
theorem isProper_of_irreducible_of_isProper_specialFibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of O)), IrreducibleSpace X → IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → (∃ x : X, f x = IsLocalRing.closedPoint O) → IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) → IsProper f := by
  intro O _ _ _ _ X f hirr hsep hlft hqc hx hfib
  obtain ⟨x₀, hx₀⟩ := hx
  have hne : Nonempty X := ⟨x₀⟩
  obtain ⟨Y, P, π, q, s, U, hπ, hUne, hiso, hproj, hq, hcomm⟩ :=
    GlobalTheory.FormalAlg.exists_isProper_isImmersion_isProjOver O X f hsep hlft hqc hne
  have hs : IsProper s := by
    obtain ⟨N, i, hi, rfl⟩ := hproj
    have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str O N
    infer_instance
  set C : Set Y := π ⁻¹' (U : Set X) with hC
  have hsurj : Function.Surjective (π ∣_ U) := fun y =>
    ⟨(inv (π ∣_ U)) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩

  have hUsub : (U : Set X) ⊆ π '' C := by
    intro u hu
    obtain ⟨v, hv⟩ := hsurj ⟨u, hu⟩
    refine ⟨v.1, v.2, ?_⟩
    have := congrArg Subtype.val hv
    rwa [morphismRestrict_base_coe] at this

  have hUirr : IsIrreducible (U : Set X) :=
    ⟨hUne, (IrreducibleSpace.isIrreducible_univ X).isPreirreducible.open_subset U.isOpen (Set.subset_univ _)⟩
  have hCirr : IsIrreducible C := by
    haveI : IrreducibleSpace (U : Set X) := Subtype.irreducibleSpace hUirr
    haveI : IrreducibleSpace (π ⁻¹ᵁ U).toScheme :=
      (Scheme.homeoOfIso (asIso (π ∣_ U))).irreducibleSpace_iff.2 (inferInstanceAs (IrreducibleSpace (U : Set X)))
    have h := (IrreducibleSpace.isIrreducible_univ (π ⁻¹ᵁ U).toScheme).image (fun y => (π ⁻¹ᵁ U).ι y)
      ((π ⁻¹ᵁ U).ι.continuous.continuousOn)
    convert h using 1
    ext y
    constructor
    · intro hy; exact ⟨⟨y, hy⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨v, -, rfl⟩; exact v.2

  have hπT : π '' closure C = Set.univ := by
    have hcl : IsClosed (π '' closure C) := π.isClosedMap _ isClosed_closure
    have hd : Dense (U : Set X) := U.isOpen.dense hUne
    refine Set.eq_univ_of_univ_subset ?_
    rw [← hd.closure_eq]
    exact closure_minimal (hUsub.trans (Set.image_mono subset_closure)) hcl
  have hmeet : ∃ y ∈ closure C, (q ≫ s) y = IsLocalRing.closedPoint O := by
    obtain ⟨y, hy, hyx⟩ : x₀ ∈ π '' closure C := hπT ▸ Set.mem_univ x₀
    refine ⟨y, hy, ?_⟩
    rw [hcomm, Scheme.Hom.comp_apply, hyx, hx₀]
  have hfib' : IsProper (pullback.snd (q ≫ s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))) := by
    rw [hcomm, (Iso.eq_inv_comp (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) π)).2
      (pullbackRightPullbackFstIso_hom_snd (f := f) (g := Spec.map (CommRingCat.ofHom (IsLocalRing.residue O))) (f' := π))]
    infer_instance
  have hclosed := GlobalTheory.T.isClosed_image_closure_completeDVR_specialFibre O Y P q s C hs hq hfib' hCirr hmeet
  have huc : UniversallyClosed f :=
    GlobalTheory.T.universallyClosed_of_closed_image_cover _ X Y P f π q s (closure C) inferInstance hq hcomm isClosed_closure hclosed hπT
  exact ⟨⟩

end GlobalTheory.FibreProper
