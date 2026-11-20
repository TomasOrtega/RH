import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

open CategoryTheory IsLocalRing

namespace GlobalTheory.LocalIndEtaleUnramified

/- English proof (translation)
Set `P : Ideal B` to `(maximalIdeal S).comap (g : B →+* S)`. Use `haveI hP : P.IsPrime := Ideal.comap_isPrime _ _`. Establish `hu : ∀ y : P.primeCompl, IsUnit (g y)`. Introduce `y`. Assume the negation of the conclusion as `h`.

Conclude with `y.2 (show (g : B →+* S) y ∈ maximalIdeal S from h)`. Set `φ : Localization.AtPrime P →ₐ[A] S` to `IsLocalization.liftAlgHom (M := P.primeCompl) hu`. Establish `hφ : ∀ y : B, φ (algebraMap B (Localization.AtPrime P) y) = g y` using `fun y => IsLocalization.lift_eq (M := P.primeCompl) (g := (g : B →+* S)) hu y`. Establish `hloc : IsLocalHom φ`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations.

Take `⟨⟨y, s⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl a`. Use `(IsLocalization.AtPrime.isUnit_mk'_iff _ P y s).2 ?_` and prove the remaining obligations. Establish `h1 : φ (IsLocalization.mk' (Localization.AtPrime P) y s) * g s = g y`. Rewrite using `[← hφ, ← map_mul, IsLocalization.mk'_spec, hφ]`. Establish `h2 : IsUnit (g y)` using `h1 ▸ ha.mul (hu s)`.

Introduce `hy`. Conclude with `(show (g : B →+* S) y ∈ maximalIdeal S from hy) h2`. Establish `hA : IsLocalHom (algebraMap A (Localization.AtPrime P))`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations. Use `ha.map φ` as an intermediate fact.

Rewrite `this` using `[AlgHom.commutes]`. Conclude with `IsLocalHom.map_nonunit a this`. Use `haveI : Algebra.FormallyUnramified B (Localization.AtPrime P) := Algebra.FormallyUnramified.of_isLocalization P.primeCompl`. Use `haveI : Algebra.EssFiniteType B (Localization.AtPrime P) := Algebra.EssFiniteType.of_isLocalization _ P.primeCompl`. Conclude with `⟨Localization.AtPrime P, inferInstance, inferInstance, inferInstance, hA, Algebra.FormallyUnramified.comp A B _, Algebra.EssFiniteType.comp A B _, φ, hloc, algebraMap B _ b, hφ b⟩`.
-/
theorem exists_local_of_algHom {A S B : Type} [CommRing A] [IsLocalRing A] [CommRing S]
    [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)] [CommRing B] [Algebra A B]
    [Algebra.FormallyUnramified A B] [Algebra.EssFiniteType A B] (g : B →ₐ[A] S) (b : B) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L),
      φ x = g b := by
  let P : Ideal B := (maximalIdeal S).comap (g : B →+* S)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hu : ∀ y : P.primeCompl, IsUnit (g y) := by
    intro y
    by_contra h
    exact y.2 (show (g : B →+* S) y ∈ maximalIdeal S from h)
  let φ : Localization.AtPrime P →ₐ[A] S := IsLocalization.liftAlgHom (M := P.primeCompl) hu
  have hφ : ∀ y : B, φ (algebraMap B (Localization.AtPrime P) y) = g y := fun y =>
    IsLocalization.lift_eq (M := P.primeCompl) (g := (g : B →+* S)) hu y
  have hloc : IsLocalHom φ := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl a
    refine (IsLocalization.AtPrime.isUnit_mk'_iff _ P y s).2 ?_
    have h1 : φ (IsLocalization.mk' (Localization.AtPrime P) y s) * g s = g y := by
      rw [← hφ, ← map_mul, IsLocalization.mk'_spec, hφ]
    have h2 : IsUnit (g y) := h1 ▸ ha.mul (hu s)
    intro hy
    exact (show (g : B →+* S) y ∈ maximalIdeal S from hy) h2
  have hA : IsLocalHom (algebraMap A (Localization.AtPrime P)) := by
    refine ⟨fun a ha => ?_⟩
    have := ha.map φ
    rw [AlgHom.commutes] at this
    exact IsLocalHom.map_nonunit a this
  haveI : Algebra.FormallyUnramified B (Localization.AtPrime P) :=
    Algebra.FormallyUnramified.of_isLocalization P.primeCompl
  haveI : Algebra.EssFiniteType B (Localization.AtPrime P) :=
    Algebra.EssFiniteType.of_isLocalization _ P.primeCompl
  exact ⟨Localization.AtPrime P, inferInstance, inferInstance, inferInstance, hA,
    Algebra.FormallyUnramified.comp A B _, Algebra.EssFiniteType.comp A B _, φ, hloc,
    algebraMap B _ b, hφ b⟩

/- English proof (translation)
Take `⟨J, _, _, D, t, c, hc, H⟩` from `h`. Take `⟨j, b, hb⟩` from `Limits.Concrete.isColimit_exists_rep D hc s`. Take `⟨hE, hcomp⟩` from `H j`. Set `f : A →+* D.obj j` to `(t.app j).hom`. Set `g₀ : D.obj j →+* S` to `(c.app j).hom`.

Use `letI : Algebra A (D.obj j) := f.toAlgebra`. Use `haveI : Algebra.Etale A (D.obj j) := hE`. Establish `hg : ∀ a : A, g₀ (f a) = algebraMap A S a` using `fun a => congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of S => k.hom a) hcomp`. Set `g : D.obj j →ₐ[A] S` to `{ g₀ with commutes' := hg }`. Establish `hb' : g b = s` using `hb`.

Rewrite using `[← hb']`. Conclude with `exists_local_of_algHom g b`.
-/
theorem exists_local_unramified_of_isIndEtale {A S : Type} [CommRing A] [IsLocalRing A]
    [CommRing S] [IsLocalRing S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A S)) (s : S) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : Algebra A L)
      (_ : IsLocalHom (algebraMap A L)) (_ : Algebra.FormallyUnramified A L)
      (_ : Algebra.EssFiniteType A L) (φ : L →ₐ[A] S) (_ : IsLocalHom φ) (x : L),
      φ x = s := by
  obtain ⟨J, _, _, D, t, c, hc, H⟩ := h
  obtain ⟨j, b, hb⟩ := Limits.Concrete.isColimit_exists_rep D hc s
  obtain ⟨hE, hcomp⟩ := H j
  let f : A →+* D.obj j := (t.app j).hom
  let g₀ : D.obj j →+* S := (c.app j).hom
  letI : Algebra A (D.obj j) := f.toAlgebra
  haveI : Algebra.Etale A (D.obj j) := hE
  have hg : ∀ a : A, g₀ (f a) = algebraMap A S a := fun a =>
    congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of S => k.hom a) hcomp
  let g : D.obj j →ₐ[A] S := { g₀ with commutes' := hg }
  have hb' : g b = s := hb
  rw [← hb']
  exact exists_local_of_algHom g b

end GlobalTheory.LocalIndEtaleUnramified
