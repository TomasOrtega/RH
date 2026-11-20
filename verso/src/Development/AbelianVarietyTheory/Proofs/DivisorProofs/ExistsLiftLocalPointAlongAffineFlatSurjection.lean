import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LiftLocal

/- English proof (translation)
Substitute `hq` using the available equality. Set `e` to `IsLocalization.atUnits R (IsLocalRing.closedPoint R).asIdeal.primeCompl (S := (Spec.structureSheaf R).presheaf.stalk (IsLocalRing.closedPoint R)) (fun y hy => by`. Rewrite using `[IsUnit.mem_submonoid_iff]`. Assume the negation of the conclusion as `h`. Conclude with `hy ((IsLocalRing.mem_maximalIdeal y).mpr h))`.

Establish `: ⇑(StructureSheaf.toStalk R (IsLocalRing.closedPoint R)).hom = ⇑e`. Use function extensionality and compare the values at `fun r => (e.commutes r).symm`. Rewrite using `[this]`. Conclude with `e.bijective`.
-/
theorem toStalk_bijective (R : Type) [CommRing R] [IsLocalRing R] (q : PrimeSpectrum R)
    (hq : q = IsLocalRing.closedPoint R) : Function.Bijective (StructureSheaf.toStalk R q).hom := by
  subst hq
  let e := IsLocalization.atUnits R (IsLocalRing.closedPoint R).asIdeal.primeCompl
    (S := (Spec.structureSheaf R).presheaf.stalk (IsLocalRing.closedPoint R)) (fun y hy => by
      rw [IsUnit.mem_submonoid_iff]
      by_contra h
      exact hy ((IsLocalRing.mem_maximalIdeal y).mpr h))
  have : ⇑(StructureSheaf.toStalk R (IsLocalRing.closedPoint R)).hom = ⇑e :=
    funext fun r => (e.commutes r).symm
  rw [this]
  exact e.bijective

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a ha => by have h2 : (RingEquiv.ofBijective f hf).symm (f a) = a := (RingEquiv.ofBijective f hf).symm_apply_apply a rw [← h2] exact ha.map _⟩`.
-/
theorem isLocalHom_of_bijective {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Bijective f) : IsLocalHom f :=
  ⟨fun a ha => by
    have h2 : (RingEquiv.ofBijective f hf).symm (f a) = a := (RingEquiv.ofBijective f hf).symm_apply_apply a
    rw [← h2]
    exact ha.map _⟩

/- English proof (translation)
Introduce `R _ _ X Y π _ _ _ x`. Take `⟨p, hp⟩` from `(pullback.fst x π).surjective (IsLocalRing.closedPoint R)`. Establish `hb` using `toStalk_bijective R _ hp`. Establish `hτ : IsLocalHom (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom` using `isLocalHom_of_bijective _ hb`. Use `letI : Algebra ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) := ((pullback.fst x π).stalkMap p).hom.toAlgebra`.

Use `haveI : Module.Flat ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) := Flat.stalkMap (pullback.fst x π) p`. Use `haveI : IsLocalHom (algebraMap ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p)) := inferInstanceAs (IsLocalHom ((pullback.fst x π).stalkMap p).hom)`. Use `haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp R).presheaf.stalk ((pullback.fst x π) p)) (B := (pullback x π).presheaf.stalk p)`. Establish `hψ : Function.Injective ((pullback.fst x π).stalkMap p).hom` using `FaithfulSMul.algebraMap_injective _ _`. Establish `hψl : IsLocalHom ((pullback.fst x π).stalkMap p).hom` using `inferInstance`.

Use `⟨(pullback x π).presheaf.stalk p, inferInstance, inferInstance, ((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom, ⟨fun a ha => hτ.map_nonunit a (hψl.map_nonunit _ ha)⟩, hψ.comp hb.1, (pullback x π).fromSpecStalk p ≫ pullback.snd x π, …` and prove the remaining obligations. Establish `hS : spMap (((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom) = Spec.map ((pullback.fst x π).stalkMap p) ≫ (Sp R).fromSpecStalk ((pullback.fst x π) p)`. Rewrite using `[Scheme.Spec_fromSpecStalk']`. Conclude with `(Spec.map_comp (StructureSheaf.toStalk R ((pullback.fst x π) p)) ((pullback.fst x π).stalkMap p))`. Rewrite using `[Category.assoc, ← pullback.condition, hS, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]`.
-/
theorem lift : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Scheme.{0}) (π : Y ⟶ X) [IsAffineHom π] [Flat π]
    [Surjective π] (x : Sp R ⟶ X), ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (φ : R →+* R'),
    IsLocalHom φ ∧ Function.Injective φ ∧ ∃ x' : Sp R' ⟶ Y, x' ≫ π = spMap φ ≫ x := by
  intro R _ _ X Y π _ _ _ x
  obtain ⟨p, hp⟩ := (pullback.fst x π).surjective (IsLocalRing.closedPoint R)
  have hb := toStalk_bijective R _ hp
  have hτ : IsLocalHom (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom := isLocalHom_of_bijective _ hb
  letI : Algebra ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) :=
    ((pullback.fst x π).stalkMap p).hom.toAlgebra
  haveI : Module.Flat ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p) :=
    Flat.stalkMap (pullback.fst x π) p
  haveI : IsLocalHom (algebraMap ((Sp R).presheaf.stalk ((pullback.fst x π) p)) ((pullback x π).presheaf.stalk p)) :=
    inferInstanceAs (IsLocalHom ((pullback.fst x π).stalkMap p).hom)
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := (Sp R).presheaf.stalk ((pullback.fst x π) p)) (B := (pullback x π).presheaf.stalk p)
  have hψ : Function.Injective ((pullback.fst x π).stalkMap p).hom := FaithfulSMul.algebraMap_injective _ _
  have hψl : IsLocalHom ((pullback.fst x π).stalkMap p).hom := inferInstance
  refine ⟨(pullback x π).presheaf.stalk p, inferInstance, inferInstance,
    ((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom,
    ⟨fun a ha => hτ.map_nonunit a (hψl.map_nonunit _ ha)⟩, hψ.comp hb.1,
    (pullback x π).fromSpecStalk p ≫ pullback.snd x π, ?_⟩
  have hS : spMap (((pullback.fst x π).stalkMap p).hom.comp (StructureSheaf.toStalk R ((pullback.fst x π) p)).hom) =
      Spec.map ((pullback.fst x π).stalkMap p) ≫ (Sp R).fromSpecStalk ((pullback.fst x π) p) := by
    rw [Scheme.Spec_fromSpecStalk']
    exact (Spec.map_comp (StructureSheaf.toStalk R ((pullback.fst x π) p)) ((pullback.fst x π).stalkMap p))
  rw [Category.assoc, ← pullback.condition, hS, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]

end GlobalTheory.LiftLocal
