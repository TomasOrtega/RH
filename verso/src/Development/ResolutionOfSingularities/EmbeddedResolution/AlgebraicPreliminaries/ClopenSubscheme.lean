import Mathlib

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Opens

/- English proof (authored)
The inclusion of an open subscheme is an open immersion and hence a preimmersion. Its image is the given open, which is closed by hypothesis. A preimmersion with closed image is a closed immersion.
-/
theorem isClosedImmersion_ι_of_isClosed {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) : IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion U.ι (by rw [U.range_ι]; exact hU)

end AlgebraicGeometry.Scheme.Opens

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The open immersion of C is also a closed immersion because its image is the closed set Z. Its defining ideal has support Z, so the vanishing ideal of Z is its radical. Inclusion into that radical factors the vanishing-ideal closed subscheme through C. The factor is a preimmersion and is surjective on points because both immersions into X have image Z and the inclusion of C is injective. Thus the factor is a closed immersion with full support. The scheme C is reduced as an open subscheme of the reduced scheme X. Its only ideal sheaf with full support is zero, since such an ideal is contained in the nilradical. The factor is therefore an isomorphism and its construction gives the stated equality over X.
-/
private theorem exists_iso_subscheme_vanishingIdeal_of_coe_eq {X : Scheme} [IsReduced X]
    (C : X.Opens) (Z : Closeds X) (hZ : (Z : Set X) = (C : Set X)) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ≅ C.toScheme,
      e.hom ≫ C.ι = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
  have hCclosed : IsClosed (C : Set X) := by rw [← hZ]; exact Z.2
  have : IsClosedImmersion C.ι :=
    IsClosedImmersion.of_isPreimmersion C.ι (by rw [C.range_ι]; exact hCclosed)
  have hkersupp : ((Scheme.Hom.ker C.ι).support : Set X) = (Z : Set X) := by
    rw [Scheme.Hom.support_ker, C.range_ι, hCclosed.closure_eq]
    exact hZ.symm
  have hZsupp : (Scheme.Hom.ker C.ι).support = Z := TopologicalSpace.Closeds.ext hkersupp
  have hvan : Scheme.IdealSheafData.vanishingIdeal Z = (Scheme.Hom.ker C.ι).radical := by
    rw [← hZsupp]
    exact Scheme.IdealSheafData.vanishingIdeal_support
  have hsupp : (Scheme.IdealSheafData.vanishingIdeal Z).support = Z := by
    rw [hvan, Scheme.IdealSheafData.support_radical]
    exact hZsupp
  have hrange :
      Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (C : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hsupp]
    exact hZ
  have hle : Scheme.Hom.ker C.ι ≤
      Scheme.Hom.ker (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hvan]
    exact Scheme.IdealSheafData.le_radical _
  let φ : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ C.toScheme :=
    IsClosedImmersion.lift C.ι (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι hle
  have hφ : φ ≫ C.ι = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι :=
    IsClosedImmersion.lift_fac _ _ hle
  have hφbase : ∀ x, ⇑C.ι (⇑φ x) =
      ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι x := by
    intro x
    rw [← hφ]
    simp
  have hinj : Function.Injective ⇑C.ι := C.ι.isOpenEmbedding.injective
  have hsurj : Function.Surjective ⇑φ := by
    intro y
    have hy : ⇑C.ι y ∈ Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι := by
      rw [hrange, ← C.range_ι]
      exact Set.mem_range_self y
    obtain ⟨x, hx⟩ := hy
    refine ⟨x, hinj ?_⟩
    rw [hφbase x]
    exact hx
  have : IsPreimmersion (φ ≫ C.ι) := by rw [hφ]; infer_instance
  have : IsPreimmersion φ := IsPreimmersion.of_comp φ C.ι
  have : IsClosedImmersion φ :=
    IsClosedImmersion.of_isPreimmersion φ (by rw [hsurj.range_eq]; exact isClosed_univ)
  have hker : Scheme.Hom.ker φ = ⊥ := by
    rw [← Scheme.IdealSheafData.support_eq_top_iff]
    refine TopologicalSpace.Closeds.ext ?_
    rw [Scheme.Hom.support_ker, hsurj.range_eq, closure_univ]
    simp
  have : IsIso φ := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  exact ⟨asIso φ, hφ⟩

/- English proof (authored)
Regard the underlying set of C as a closed subset using the given closedness. This closed subset has exactly the same points as C, so apply the comparison of the vanishing-ideal subscheme with the corresponding open subscheme.
-/
theorem exists_iso_subscheme_vanishingIdeal_of_isClosed
    {X : Scheme} [IsReduced X] (C : X.Opens) (hC : IsClosed (C : Set X)) :
    ∃ e : (Scheme.IdealSheafData.vanishingIdeal
        (⟨(C : Set X), hC⟩ : TopologicalSpace.Closeds X)).subscheme ≅ C.toScheme,
      e.hom ≫ C.ι =
        (Scheme.IdealSheafData.vanishingIdeal
          (⟨(C : Set X), hC⟩ : TopologicalSpace.Closeds X)).subschemeι :=
  exists_iso_subscheme_vanishingIdeal_of_coe_eq C _ rfl

def complOpensOfIsClosed {X : Scheme} (C : X.Opens) (hC : IsClosed (C : Set X)) : X.Opens :=
  ⟨(C : Set X)ᶜ, hC.isOpen_compl⟩

@[simp]
/- English proof (authored)
The complement of the underlying set of C is open by closedness. The indicated open is constructed from this complement, so its underlying set is that complement.
-/
theorem coe_complOpensOfIsClosed {X : Scheme} (C : X.Opens) (hC : IsClosed (C : Set X)) :
    ((complOpensOfIsClosed C hC : X.Opens) : Set X) = (C : Set X)ᶜ := rfl

end FunctorialResolution.EmbeddedResolution
