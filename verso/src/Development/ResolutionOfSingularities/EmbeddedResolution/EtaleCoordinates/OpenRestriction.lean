import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace OpenImmersionRestriction

/- English proof (authored)
The closed subscheme defined by the pulled-back ideal on V is the fibre product of V and the closed subscheme defined by D over W. Take its projection to the latter closed subscheme. That projection is the base change of the open immersion V → W, so it is an open immersion. The fibre product square gives the required equality of composites.
-/
private theorem exists_subschemeMap_isOpenImmersion {V W : Scheme.{u}} (f : V ⟶ W)
    [IsOpenImmersion f] (D : W.IdealSheafData) :
    ∃ g : (D.comap f).subscheme ⟶ D.subscheme,
      IsOpenImmersion g ∧ g ≫ D.subschemeι = (D.comap f).subschemeι ≫ f := by
  have h₁ : IsOpenImmersion (Limits.pullback.snd f D.subschemeι) := inferInstance
  have h₂ : IsOpenImmersion (D.comapIso f).hom := inferInstance
  refine ⟨(D.comapIso f).hom ≫ Limits.pullback.snd f D.subschemeι, inferInstance, ?_⟩
  rw [Category.assoc, ← Limits.pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

/- English proof (authored)
The fibre product construction supplies an open immersion with the required composite into W. Any other map with the same composite agrees with it because the closed immersion into W is a monomorphism. The given map is therefore an open immersion.
-/
theorem isOpenImmersion_subschemeMap {V W : Scheme.{u}} (f : V ⟶ W) [IsOpenImmersion f]
    (D : W.IdealSheafData) (g : (D.comap f).subscheme ⟶ D.subscheme)
    (hg : g ≫ D.subschemeι = (D.comap f).subschemeι ≫ f) :
    IsOpenImmersion g := by
  obtain ⟨g', hg', hg'fac⟩ := exists_subschemeMap_isOpenImmersion f D
  have : Mono D.subschemeι := inferInstance
  have heq : g = g' := by
    refine (cancel_mono D.subschemeι).mp ?_
    rw [hg, hg'fac]
  rw [heq]
  exact hg'

/- English proof (authored)
Restricting to an open subscheme preserves the local description by one non-zero-divisor. The pulled-back closed subscheme maps to the original divisor by an open immersion, which is smooth. Composing it with the original divisor's smooth map to the base field gives the smooth structure map of the pulled-back divisor.
-/
theorem isSmoothDivisor_comap {V W : Scheme.{u}} {k : Type u} [Field k]
    (f : V ⟶ W) [IsOpenImmersion f] (p : W ⟶ Spec (CommRingCat.of k))
    (D : W.IdealSheafData) (hD : IsSmoothDivisor p D) :
    IsSmoothDivisor (f ≫ p) (D.comap f) := by
  obtain ⟨g, hg, hgfac⟩ := exists_subschemeMap_isOpenImmersion f D
  refine ⟨hD.1.comap_of_isOpenImmersion f, ?_⟩
  have : IsOpenImmersion g := hg
  have : AlgebraicGeometry.Smooth g := inferInstance
  have hsm : AlgebraicGeometry.Smooth (D.subschemeι ≫ p) := hD.2
  have hcomp : (D.comap f).subschemeι ≫ f ≫ p = g ≫ D.subschemeι ≫ p := by
    rw [← Category.assoc, ← hgfac, Category.assoc]
  rw [hcomp]
  infer_instance

end OpenImmersionRestriction

end FunctorialResolution.EmbeddedResolution
