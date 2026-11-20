import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionSmoothAffineSurjectiveFourierTermsStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatSurjectiveKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

/- English proof (translation)
Introduce `Y Z φ H`. Establish `H' : ∀ y : Y, ∃ U : Z.Opens, φ y ∈ U ∧ IsClosedImmersion (φ ∣_ U)`. Introduce `y`. Take `⟨U, W, h, hU, hy, hW, hWa, hs⟩` from `H y`. Take `rfl : W = φ ⁻¹ᵁ U` from `le_antisymm h hW`.

Use `⟨U, hy, ?_⟩` and prove the remaining obligations. Establish `: IsAffine U` using `hU`. Establish `: IsAffine (φ ⁻¹ᵁ U)` using `hWa`. Rewrite using `[MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion (Arrow.isoMk hWa.isoSpec hU.isoSpec (Scheme.Opens.toSpecΓ_naturality φ _) : Arrow.mk (φ ∣_ U) ≅ Arrow.mk (Spec.map (φ.app U)))]`. Rewrite using `[Scheme.Hom.app_eq_appLE]`.

Conclude with `IsClosedImmersion.spec_of_surjective _ hs`. Use `choose U hyU hU using H'`. Establish `: MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion` using `⟨fun i hi g hg => by`. Establish `: IsOpenImmersion i` using `hi`. Establish `: IsImmersion g` using `hg`.

Use the proof step `infer_instance⟩`. Use `IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) U ?_ fun y => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, rfl⟩`. Conclude with `(le_iSup U y : U y ≤ ⨆ i, U i) (hyU y)`. Use `hU y infer_instance` as an intermediate fact.
-/
theorem isImmersion_of_forall_affine_surjective_appLE : ∀ (Y Z : Scheme.{0}) (φ : Y ⟶ Z), (∀ y : Y, ∃ (U : Z.Opens) (W : Y.Opens) (h : W ≤ φ ⁻¹ᵁ U), IsAffineOpen U ∧ φ y ∈ U ∧ φ ⁻¹ᵁ U ≤ W ∧ IsAffineOpen W ∧ Function.Surjective (φ.appLE U W h).hom) → IsImmersion φ := by
  intro Y Z φ H
  have H' : ∀ y : Y, ∃ U : Z.Opens, φ y ∈ U ∧ IsClosedImmersion (φ ∣_ U) := by
    intro y
    obtain ⟨U, W, h, hU, hy, hW, hWa, hs⟩ := H y
    obtain rfl : W = φ ⁻¹ᵁ U := le_antisymm h hW
    refine ⟨U, hy, ?_⟩
    have : IsAffine U := hU
    have : IsAffine (φ ⁻¹ᵁ U) := hWa
    rw [MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
      (Arrow.isoMk hWa.isoSpec hU.isoSpec (Scheme.Opens.toSpecΓ_naturality φ _) :
        Arrow.mk (φ ∣_ U) ≅ Arrow.mk (Spec.map (φ.app U)))]
    rw [Scheme.Hom.app_eq_appLE]
    exact IsClosedImmersion.spec_of_surjective _ hs
  choose U hyU hU using H'
  have : MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion :=
    ⟨fun i hi g hg => by
      have : IsOpenImmersion i := hi
      have : IsImmersion g := hg
      infer_instance⟩
  refine IsZariskiLocalAtTarget.of_range_subset_iSup (P := @IsImmersion) U ?_ fun y => ?_
  · rintro _ ⟨y, rfl⟩
    exact (le_iSup U y : U y ≤ ⨆ i, U i) (hyU y)
  · have := hU y
    infer_instance

end GlobalTheory
