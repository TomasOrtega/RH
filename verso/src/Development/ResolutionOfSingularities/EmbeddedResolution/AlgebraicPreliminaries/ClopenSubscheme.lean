import Mathlib

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Opens

/- English proof (translation)
The claim follows from `IsClosedImmersion.of_isPreimmersion U.ι (by rw [U.range_ι]; exact hU)`.
-/
theorem isClosedImmersion_ι_of_isClosed {X : Scheme.{u}} (U : X.Opens)
    (hU : IsClosed (U : Set X)) : IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion U.ι (by rw [U.range_ι]; exact hU)

end AlgebraicGeometry.Scheme.Opens

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Establish `hCclosed : IsClosed (C : Set X)` using `by rw [← hZ]; exact Z.2`. Establish `: IsClosedImmersion C.ι` using `IsClosedImmersion.of_isPreimmersion C.ι (by rw [C.range_ι]; exact hCclosed)`. Establish `hkersupp : ((Scheme.Hom.ker C.ι).support : Set X) = (Z : Set X)`. Rewrite using `[Scheme.Hom.support_ker, C.range_ι, hCclosed.closure_eq]`. Conclude with `hZ.symm`.

Establish `hZsupp : (Scheme.Hom.ker C.ι).support = Z` using `TopologicalSpace.Closeds.ext hkersupp`. Establish `hvan : Scheme.IdealSheafData.vanishingIdeal Z = (Scheme.Hom.ker C.ι).radical`. Rewrite using `[← hZsupp]`. Conclude with `Scheme.IdealSheafData.vanishingIdeal_support`. Establish `hsupp : (Scheme.IdealSheafData.vanishingIdeal Z).support = Z`.

Rewrite using `[hvan, Scheme.IdealSheafData.support_radical]`. Conclude with `hZsupp`. Establish `hrange : Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι = (C : Set X)`. Rewrite using `[Scheme.IdealSheafData.range_subschemeι, hsupp]`. Conclude with `hZ`.

Establish `hle : Scheme.Hom.ker C.ι ≤ Scheme.Hom.ker (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι`. Rewrite using `[Scheme.IdealSheafData.ker_subschemeι, hvan]`. Conclude with `Scheme.IdealSheafData.le_radical _`. Set `φ : (Scheme.IdealSheafData.vanishingIdeal Z).subscheme ⟶ C.toScheme` to `IsClosedImmersion.lift C.ι (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι hle`. Establish `hφ : φ ≫ C.ι = (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι` using `IsClosedImmersion.lift_fac _ _ hle`.

Establish `hφbase : ∀ x, ⇑C.ι (⇑φ x) = ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι x`. Introduce `x`. Rewrite using `[← hφ]`. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective ⇑C.ι` using `C.ι.isOpenEmbedding.injective`.

Establish `hsurj : Function.Surjective ⇑φ`. Introduce `y`. Establish `hy : ⇑C.ι y ∈ Set.range ⇑(Scheme.IdealSheafData.vanishingIdeal Z).subschemeι`. Rewrite using `[hrange, ← C.range_ι]`. Conclude with `Set.mem_range_self y`.

Take `⟨x, hx⟩` from `hy`. Use `⟨x, hinj ?_⟩` and prove the remaining obligations. Rewrite using `[hφbase x]`. Conclude with `hx`. Establish `: IsPreimmersion (φ ≫ C.ι)` using `by rw [hφ]; infer_instance`.

Establish `: IsPreimmersion φ` using `IsPreimmersion.of_comp φ C.ι`. Establish `: IsClosedImmersion φ` using `IsClosedImmersion.of_isPreimmersion φ (by rw [hsurj.range_eq]; exact isClosed_univ)`. Establish `hker : Scheme.Hom.ker φ = ⊥`. Rewrite using `[← Scheme.IdealSheafData.support_eq_top_iff]`. Use `TopologicalSpace.Closeds.ext ?_` and prove the remaining obligations.

Rewrite using `[Scheme.Hom.support_ker, hsurj.range_eq, closure_univ]`. Simplify using the standard rewrite rules. Establish `: IsIso φ` using `IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker`. Conclude with `⟨asIso φ, hφ⟩`.
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

/- English proof (translation)
The claim follows from `exists_iso_subscheme_vanishingIdeal_of_coe_eq C _ rfl`.
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
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_complOpensOfIsClosed {X : Scheme} (C : X.Opens) (hC : IsClosed (C : Set X)) :
    ((complOpensOfIsClosed C hC : X.Opens) : Set X) = (C : Set X)ᶜ := rfl

end FunctorialResolution.EmbeddedResolution
