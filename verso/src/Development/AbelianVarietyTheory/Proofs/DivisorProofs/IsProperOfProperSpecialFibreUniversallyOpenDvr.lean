import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.CompletionDVR
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIrreducibleProperSpecialFibreCompleteDStatement

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.FibreProperDvr

/- English proof (translation)
Introduce `W _ _ _ X f h1 h2 h3 h4 h5 h6`. Take `⟨⟨hdom, hdvr⟩, hcpl, -, hloc, -⟩` from `ReciprocityTheory.CA.Pt.completionDVR W`. Set `O` to `AdicCompletion (maximalIdeal W) W`. Use `haveI : Module.Flat W O := AdicCompletion.flat_of_isNoetherian _`. Use `haveI : Module.FaithfullyFlat W O := Module.FaithfullyFlat.of_flat_of_isLocalHom`.

Set `g : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of W)` to `Spec.map (CommRingCat.ofHom (algebraMap W O))`. Establish `gfl : Flat g`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Conclude with `RingHom.flat_algebraMap_iff.2 inferInstance`. Establish `gsurj : Surjective g` using `⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := W) (B := O)⟩`.

Use `haveI : IrreducibleSpace (Spec (CommRingCat.of O)) := inferInstance`. Use `haveI : IrreducibleSpace ↥(pullback f g) := inferInstance`. Set `k` to `CommRingCat.ofHom (IsLocalRing.residue W)`. Set `kO` to `CommRingCat.ofHom (IsLocalRing.residue O)`. Set `ψ` to `CommRingCat.ofHom (IsLocalRing.ResidueField.map (algebraMap W O))`.

Establish `hsq : Spec.map kO ≫ g = Spec.map ψ ≫ Spec.map k`. Simplify using `only [g, ← Spec.map_comp]`. Use `congr 1`. Establish `hsp : IsProper (pullback.snd (pullback.snd f g) (Spec.map kO))`. Rewrite using `[← pullbackLeftPullbackSndIso_hom_snd f g (Spec.map kO)]`.

Establish `: IsProper (pullback.snd f (Spec.map kO ≫ g))`. Rewrite using `[hsq, ← MorphismProperty.cancel_left_of_respectsIso @IsProper (pullbackLeftPullbackSndIso f (Spec.map k) (Spec.map ψ)).hom, pullbackLeftPullbackSndIso_hom_snd]`. Use `infer_instance`. Use `infer_instance`. Establish `hex : ∃ x : ↥(pullback f g), (pullback.snd f g) x = IsLocalRing.closedPoint O` using `(pullback.snd f g).surjective _`.

Establish `hp : IsProper (pullback.snd f g)` using `GlobalTheory.T.isProper_of_irreducible_properSpecialFibre_completeDvr O (pullback f g) (pullback.snd f g) inferInstance inferInstance inferInstance inferInstance hex hsp`. Establish `hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) g` using `⟨⟨gsurj, gfl⟩, inferInstance⟩`. Establish `: UniversallyClosed f` using `MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu hp.toUniversallyClosed`. Conclude with `⟨⟩`.
-/
theorem isProper_of_specialFibre : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of W)), IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    UniversallyOpen f → GeometricallyIrreducible f →
    IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue W)))) → IsProper f := by
  intro W _ _ _ X f h1 h2 h3 h4 h5 h6
  obtain ⟨⟨hdom, hdvr⟩, hcpl, -, hloc, -⟩ := ReciprocityTheory.CA.Pt.completionDVR W
  let O := AdicCompletion (maximalIdeal W) W
  haveI : Module.Flat W O := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat W O := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let g : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of W) := Spec.map (CommRingCat.ofHom (algebraMap W O))
  have gfl : Flat g := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have gsurj : Surjective g := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := W) (B := O)⟩
  haveI : IrreducibleSpace (Spec (CommRingCat.of O)) := inferInstance
  haveI : IrreducibleSpace ↥(pullback f g) := inferInstance

  let k := CommRingCat.ofHom (IsLocalRing.residue W)
  let kO := CommRingCat.ofHom (IsLocalRing.residue O)
  let ψ := CommRingCat.ofHom (IsLocalRing.ResidueField.map (algebraMap W O))
  have hsq : Spec.map kO ≫ g = Spec.map ψ ≫ Spec.map k := by
    simp only [g, ← Spec.map_comp]
    congr 1
  have hsp : IsProper (pullback.snd (pullback.snd f g) (Spec.map kO)) := by
    rw [← pullbackLeftPullbackSndIso_hom_snd f g (Spec.map kO)]
    have : IsProper (pullback.snd f (Spec.map kO ≫ g)) := by
      rw [hsq, ← MorphismProperty.cancel_left_of_respectsIso @IsProper
        (pullbackLeftPullbackSndIso f (Spec.map k) (Spec.map ψ)).hom, pullbackLeftPullbackSndIso_hom_snd]
      infer_instance
    infer_instance
  have hex : ∃ x : ↥(pullback f g), (pullback.snd f g) x = IsLocalRing.closedPoint O :=
    (pullback.snd f g).surjective _
  have hp : IsProper (pullback.snd f g) :=
    GlobalTheory.T.isProper_of_irreducible_properSpecialFibre_completeDvr O (pullback f g) (pullback.snd f g) inferInstance inferInstance inferInstance inferInstance hex hsp
  have hu : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) g :=
    ⟨⟨gsurj, gfl⟩, inferInstance⟩
  have : UniversallyClosed f :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := @UniversallyClosed) hu hp.toUniversallyClosed
  exact ⟨⟩

end GlobalTheory.FibreProperDvr
