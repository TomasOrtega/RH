import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

/- English proof (translation)
Establish `hm : (RingHom.ker φ).IsMaximal`. Establish `: (RingHom.ker φ).IsPrime` using `RingHom.ker_isPrime φ`. Conclude with `IsArtinianRing.isMaximal_of_isPrime _`. Establish `he : RingHom.ker φ = IsLocalRing.maximalIdeal A` using `IsLocalRing.eq_maximalIdeal hm`. Establish `H : ∀ a ∈ IsLocalRing.maximalIdeal A, φ a = 0` using `fun a ha => by`.

Rewrite `ha` using `[← he]`. Conclude with `(RingHom.mem_ker).1 ha`. Conclude with `⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) φ H, RingHom.ext fun a => Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal A) φ H⟩`.
-/
theorem exists_comp_residue_eq (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (K : Type) [Field K] (φ : A →+* K) :
    ∃ ψ : IsLocalRing.ResidueField A →+* K, ψ.comp (IsLocalRing.residue A) = φ := by
  have hm : (RingHom.ker φ).IsMaximal := by
    have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    exact IsArtinianRing.isMaximal_of_isPrime _
  have he : RingHom.ker φ = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hm
  have H : ∀ a ∈ IsLocalRing.maximalIdeal A, φ a = 0 := fun a ha => by
    rw [← he] at ha
    exact (RingHom.mem_ker).1 ha
  exact ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) φ H,
    RingHom.ext fun a => Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal A) φ H⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `K _ y Z fst snd hpb`. Take `⟨ψ, hψ⟩` from `exists_comp_residue_eq A K (Spec.preimage y).hom`. Establish `hy : Spec.map (CommRingCat.ofHom ψ) ≫ spMap (IsLocalRing.residue A) = y`. Rewrite using `[spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_hom]`.

Conclude with `Spec.map_preimage y`. Establish `hw : fst ≫ p = (snd ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ spMap (IsLocalRing.residue A)`. Rewrite using `[Category.assoc, hy]`. Conclude with `hpb.w`. Establish `hbig : IsPullback (pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) hw ≫ pullback.fst p (spMap (IsLocalRing.residue A))) snd p (Spec.map (CommRingCat.ofHom ψ) ≫ spMap (IsLocalRing.residue A))`.

Rewrite using `[pullback.lift_fst, hy]`. Conclude with `hpb`. Establish `hsq : IsPullback (pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) hw) snd (pullback.snd p (spMap (IsLocalRing.residue A))) (Spec.map (CommRingCat.ofHom ψ))` using `IsPullback.of_right hbig (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)`. Conclude with `h.geometrically_isIntegral (Spec.map (CommRingCat.ofHom ψ)) _ snd hsq`.
-/
theorem geometricallyIntegral_of_closedFibre (A : Type) [CommRing A] [IsLocalRing A]
    [IsArtinianRing A] (X : Scheme.{0}) (p : X ⟶ Sp A)
    (h : GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A)))) :
    GeometricallyIntegral p := by
  constructor
  intro K _ y Z fst snd hpb
  obtain ⟨ψ, hψ⟩ := exists_comp_residue_eq A K (Spec.preimage y).hom
  have hy : Spec.map (CommRingCat.ofHom ψ) ≫ spMap (IsLocalRing.residue A) = y := by
    rw [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ, CommRingCat.ofHom_hom]
    exact Spec.map_preimage y
  have hw : fst ≫ p = (snd ≫ Spec.map (CommRingCat.ofHom ψ)) ≫ spMap (IsLocalRing.residue A) := by
    rw [Category.assoc, hy]
    exact hpb.w
  have hbig : IsPullback (pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) hw ≫
      pullback.fst p (spMap (IsLocalRing.residue A))) snd p
      (Spec.map (CommRingCat.ofHom ψ) ≫ spMap (IsLocalRing.residue A)) := by
    rw [pullback.lift_fst, hy]
    exact hpb
  have hsq : IsPullback (pullback.lift fst (snd ≫ Spec.map (CommRingCat.ofHom ψ)) hw) snd
      (pullback.snd p (spMap (IsLocalRing.residue A))) (Spec.map (CommRingCat.ofHom ψ)) :=
    IsPullback.of_right hbig (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  exact h.geometrically_isIntegral (Spec.map (CommRingCat.ofHom ψ)) _ snd hsq

/- English proof (translation)
Introduce `A _ _ _ X p hflat hprop hgi`. Use `haveI : IsAffine (Sp A) := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))`. Use `haveI : IsLocallyNoetherian (Sp A) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of A)))`. Use `haveI := hflat`. Use `haveI := hprop`.

Use `haveI : GeometricallyIntegral p := geometricallyIntegral_of_closedFibre A X p hgi`. Conclude with `GlobalTheory.ProperFunctions.isIso_appTop_of_isAffine p`.
-/
theorem isIso_appTop_of_artinian : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (X : Scheme.{0}) (p : X ⟶ Sp A), Flat p → IsProper p →
    GeometricallyIntegral (pullback.snd p (spMap (IsLocalRing.residue A))) → IsIso p.appTop := by
  intro A _ _ _ X p hflat hprop hgi
  haveI : IsAffine (Sp A) := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  haveI : IsLocallyNoetherian (Sp A) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of A)))
  haveI := hflat
  haveI := hprop
  haveI : GeometricallyIntegral p := geometricallyIntegral_of_closedFibre A X p hgi
  exact GlobalTheory.ProperFunctions.isIso_appTop_of_isAffine p

end GlobalTheory.CompanionTheory.Ar.Approx
