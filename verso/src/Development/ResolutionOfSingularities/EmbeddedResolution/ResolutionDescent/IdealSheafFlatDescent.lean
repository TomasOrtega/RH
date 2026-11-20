import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IdealSheafFlatComapInjective
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
universe u

open CategoryTheory Limits AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The image operation on ideal sheaves is defined by taking the kernel of the closed subscheme inclusion followed by the given morphism.
-/
private theorem map_eq_ker {X Y : Scheme.{u}} (I : X.IdealSheafData) (f : X ⟶ Y) :
    I.map f = (I.subschemeι ≫ f).ker := rfl

/- English proof (authored)
The pullback ideal defines the base change of the closed subscheme along the morphism. Its ideal is the kernel of the resulting closed immersion, which is the first pullback projection.
-/
private theorem comap_eq_ker_pullback_fst {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) :
    I.comap f = (pullback.fst f I.subschemeι).ker := rfl

/- English proof (authored)
Form the closed subscheme defined by the ideal and pull its inclusion back to the new source. Pasting the two pullback squares shows that its map to the new target is the flat base change of the original closed subscheme’s map to the old target. This original map is quasi-compact, so its kernel commutes with flat base change. The two kernels describe the pullback of the old image ideal and the image of the pulled-back ideal, respectively.
-/
theorem comap_map_eq_map_comap_of_isPullback {W X X' W' : Scheme.{u}} {f : W ⟶ X} {g : X' ⟶ X}
    {g' : W' ⟶ W} {f' : W' ⟶ X'} (H : IsPullback g' f' f g)
    [QuasiCompact f] [AlgebraicGeometry.Flat g] (I : W.IdealSheafData) :
    (I.map f).comap g = (I.comap g').map f' := by
  have hqc : QuasiCompact (I.subschemeι ≫ f) := inferInstance
  have S : IsPullback (pullback.snd g' I.subschemeι) (pullback.fst g' I.subschemeι ≫ f')
      (I.subschemeι ≫ f) g := (IsPullback.of_hasPullback g' I.subschemeι).flip.paste_vert H
  have hqc' : QuasiCompact (pullback.fst g' I.subschemeι ≫ f') := quasiCompact_of_isPullback S
  have h1 := ker_eq_comap_ker_of_isPullback_of_flat S
  rw [map_eq_ker, ← h1, Scheme.Hom.ker_comp, comap_eq_ker_pullback_fst]

/- English proof (authored)
Flat base change on the self-pullback identifies the pullback of the image ideal with the image along the second projection of the ideal pulled back along the first. By assumption the two pulled-back ideals agree. The desired equality thus reduces to taking the image along the second projection of the ideal pulled back along it. One containment is the unit of the ideal pullback and image adjunction. For the other, pull the adjunction counit back along the diagonal section of the projection. Because the projection after this section is the identity, the resulting containment is the reverse one.
-/
theorem comap_map_eq_self_of_isPullback {W X Q : Scheme.{u}} (γ : W ⟶ X)
    [QuasiCompact γ] [AlgebraicGeometry.Flat γ] {p q : Q ⟶ W} (H : IsPullback p q γ γ)
    (I : W.IdealSheafData) (hI : I.comap p = I.comap q) :
    (I.map γ).comap γ = I := by
  have key := comap_map_eq_map_comap_of_isPullback H I
  rw [hI] at key
  rw [key]
  obtain ⟨s, hsq⟩ : ∃ s : W ⟶ Q, s ≫ q = 𝟙 W :=
    ⟨H.lift (𝟙 W) (𝟙 W) rfl, H.lift_snd _ _ _⟩
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_map_comap I q)
  have h1 := Scheme.IdealSheafData.comap_map_le (I.comap q) q
  have h2 : (((I.comap q).map q).comap q).comap s ≤ ((I.comap q).comap s) :=
    Scheme.IdealSheafData.comap_mono s h1
  rwa [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, hsq,
    Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id] at h2

end FunctorialResolution.EmbeddedResolution
