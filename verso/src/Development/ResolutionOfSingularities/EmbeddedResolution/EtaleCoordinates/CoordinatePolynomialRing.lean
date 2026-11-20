import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothRegular
universe u

namespace FunctorialResolution.EmbeddedResolution

@[reducible] def CoordPolynomialRing (k : Type u) [Field k] (m : ℕ) : Type u :=
  MvPolynomial (ULift.{u} (Fin m)) k

noncomputable def etaleChartCoord (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] (j : Fin m) : S :=
  algebraMap (CoordPolynomialRing k m) S (MvPolynomial.X (ULift.up.{u} j))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem etaleChartCoord_def (k : Type u) [Field k] (m : ℕ) (S : Type u) [CommRing S]
    [Algebra (CoordPolynomialRing k m) S] (j : Fin m) :
    etaleChartCoord k m S j =
      algebraMap (CoordPolynomialRing k m) S (MvPolynomial.X (ULift.up.{u} j)) :=
  rfl

/- English proof (translation)
Use `hp` as an intermediate fact. Use `infer_instance`.
-/
private theorem isRegularLocalRing_localization_coordPolynomialRing (k : Type u) [Field k] (m : ℕ)
    (p : Ideal (CoordPolynomialRing k m)) (hp : p.IsPrime) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have := hp
  infer_instance

/- English proof (translation)
Establish `: Algebra.FiniteType P S` using `inferInstance`. Establish `: IsNoetherianRing S` using `Algebra.FiniteType.isNoetherianRing P S`. Establish `: IsNoetherianRing A` using `IsLocalization.isNoetherianRing q.primeCompl A inferInstance`. Establish `: IsLocalRing A` using `IsLocalization.AtPrime.isLocalRing A q`. Set `: Algebra P A` to `((algebraMap S A).comp (algebraMap P S)).toAlgebra`.

Establish `: IsScalarTower P S A` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: Module.Flat P S` using `inferInstance`. Establish `: Module.Flat S A` using `IsLocalization.flat A q.primeCompl`. Establish `: Module.Flat P A` using `Module.Flat.trans P S A`. Establish `: Algebra.FormallyUnramified P S` using `inferInstance`.

Establish `: Algebra.FormallyUnramified S A` using `Algebra.FormallyUnramified.of_isLocalization q.primeCompl`. Establish `: Algebra.FormallyUnramified P A` using `Algebra.FormallyUnramified.comp P S A`. Establish `: Algebra.EssFiniteType P S` using `inferInstance`. Establish `: Algebra.EssFiniteType S A` using `Algebra.EssFiniteType.of_isLocalization A q.primeCompl`. Establish `: Algebra.EssFiniteType P A` using `Algebra.EssFiniteType.comp P S A`.

Establish `hunits : ∀ y : (q.comap (algebraMap P S)).primeCompl, IsUnit (algebraMap P A (y : P))`. Introduce and unpack `⟨y, hy⟩`. Establish `hy' : algebraMap P S y ∈ q.primeCompl` using `hy`. Establish `h` using `IsLocalization.map_units A ⟨algebraMap P S y, hy'⟩`. Rewrite using `[IsScalarTower.algebraMap_apply P S A]`.

Conclude with `h`. Set `: Algebra (Localization.AtPrime (q.comap (algebraMap P S))) A` to `(IsLocalization.lift hunits).toAlgebra`. Establish `: IsScalarTower P (Localization.AtPrime (q.comap (algebraMap P S))) A` using `IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunits x).symm`. Establish `: Module.Flat (Localization.AtPrime (q.comap (algebraMap P S))) A` using `(Module.flat_iff_of_isLocalization (Localization.AtPrime (q.comap (algebraMap P S))) (q.comap (algebraMap P S)).primeCompl A).mpr ‹_›`. Establish `: Algebra.FormallyUnramified (Localization.AtPrime (q.comap (algebraMap P S))) A` using `Algebra.FormallyUnramified.localization_base (M := (q.comap (algebraMap P S)).primeCompl)`.

Establish `: Algebra.EssFiniteType (Localization.AtPrime (q.comap (algebraMap P S))) A` using `Algebra.EssFiniteType.of_comp P (Localization.AtPrime (q.comap (algebraMap P S))) A`. Establish `: IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap P S)))` using `hreg _`. Establish `: IsLocalHom (algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A)`. Prove the components needed by the constructor for the conclusion. Introduce `r hr`.

Take `⟨⟨x, s⟩, hx⟩` from `IsLocalization.surj (M := (q.comap (algebraMap P S)).primeCompl) r`. Establish `hxA : algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A r * algebraMap P A (s : P) = algebraMap P A x`. Establish `h` using `congrArg (algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A) hx`. Rewrite `h` using `[map_mul]`. Rewrite using `[IsScalarTower.algebraMap_apply P (Localization.AtPrime (q.comap (algebraMap P S))) A (s : P), IsScalarTower.algebraMap_apply P (Localization.AtPrime (q.comap (algebraMap P S))) A x]`.

Conclude with `h`. Establish `h2 : IsUnit (algebraMap P A x)`. Rewrite using `[← hxA]`. Conclude with `hr.mul (hunits s)`. Establish `h3 : IsUnit (algebraMap S A (algebraMap P S x))`.

Rewrite using `[← IsScalarTower.algebraMap_apply P S A]`. Conclude with `h2`. Establish `h4 : algebraMap P S x ∈ q.primeCompl` using `(IsLocalization.AtPrime.isUnit_to_map_iff A q (algebraMap P S x)).mp h3`. Establish `h5 : x ∈ (q.comap (algebraMap P S)).primeCompl` using `h4`. Establish `h6 : IsUnit (algebraMap P (Localization.AtPrime (q.comap (algebraMap P S))) x)` using `IsLocalization.map_units _ ⟨x, h5⟩`.

Rewrite `h6` using `[← hx]`. Conclude with `(IsUnit.mul_iff.mp h6).1`. Conclude with `⟨isRegularLocalRing_of_flat_formallyUnramified (Localization.AtPrime (q.comap (algebraMap P S))) A, ringKrullDim_eq_of_flat_formallyUnramified (Localization.AtPrime (q.comap (algebraMap P S))) A⟩`.
-/
private theorem isRegularLocalRing_and_ringKrullDim_eq_of_etale (P S : Type u) [CommRing P] [CommRing S] [Algebra P S]
    [Algebra.Etale P S] [IsNoetherianRing P]
    (hreg : ∀ (p : Ideal P) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] :
    IsRegularLocalRing A ∧
      ringKrullDim A = ringKrullDim (Localization.AtPrime (q.comap (algebraMap P S))) := by
  have : Algebra.FiniteType P S := inferInstance
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing P S
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing q.primeCompl A inferInstance
  have : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A q
  let : Algebra P A := ((algebraMap S A).comp (algebraMap P S)).toAlgebra
  have : IsScalarTower P S A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Module.Flat P S := inferInstance
  have : Module.Flat S A := IsLocalization.flat A q.primeCompl
  have : Module.Flat P A := Module.Flat.trans P S A
  have : Algebra.FormallyUnramified P S := inferInstance
  have : Algebra.FormallyUnramified S A :=
    Algebra.FormallyUnramified.of_isLocalization q.primeCompl
  have : Algebra.FormallyUnramified P A := Algebra.FormallyUnramified.comp P S A
  have : Algebra.EssFiniteType P S := inferInstance
  have : Algebra.EssFiniteType S A := Algebra.EssFiniteType.of_isLocalization A q.primeCompl
  have : Algebra.EssFiniteType P A := Algebra.EssFiniteType.comp P S A
  have hunits : ∀ y : (q.comap (algebraMap P S)).primeCompl, IsUnit (algebraMap P A (y : P)) := by
    rintro ⟨y, hy⟩
    have hy' : algebraMap P S y ∈ q.primeCompl := hy
    have h := IsLocalization.map_units A ⟨algebraMap P S y, hy'⟩
    rw [IsScalarTower.algebraMap_apply P S A]
    exact h
  let : Algebra (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    (IsLocalization.lift hunits).toAlgebra
  have : IsScalarTower P (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunits x).symm
  have : Module.Flat (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime (q.comap (algebraMap P S)))
      (q.comap (algebraMap P S)).primeCompl A).mpr ‹_›
  have : Algebra.FormallyUnramified (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    Algebra.FormallyUnramified.localization_base (M := (q.comap (algebraMap P S)).primeCompl)
  have : Algebra.EssFiniteType (Localization.AtPrime (q.comap (algebraMap P S))) A :=
    Algebra.EssFiniteType.of_comp P (Localization.AtPrime (q.comap (algebraMap P S))) A
  have : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap P S))) :=
    hreg _
  have : IsLocalHom (algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A) := by
    constructor
    intro r hr
    obtain ⟨⟨x, s⟩, hx⟩ :=
      IsLocalization.surj (M := (q.comap (algebraMap P S)).primeCompl) r
    have hxA : algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A r
        * algebraMap P A (s : P) = algebraMap P A x := by
      have h := congrArg (algebraMap (Localization.AtPrime (q.comap (algebraMap P S))) A) hx
      rw [map_mul] at h
      rw [IsScalarTower.algebraMap_apply P
            (Localization.AtPrime (q.comap (algebraMap P S))) A (s : P),
        IsScalarTower.algebraMap_apply P
            (Localization.AtPrime (q.comap (algebraMap P S))) A x]
      exact h
    have h2 : IsUnit (algebraMap P A x) := by
      rw [← hxA]
      exact hr.mul (hunits s)
    have h3 : IsUnit (algebraMap S A (algebraMap P S x)) := by
      rw [← IsScalarTower.algebraMap_apply P S A]
      exact h2
    have h4 : algebraMap P S x ∈ q.primeCompl :=
      (IsLocalization.AtPrime.isUnit_to_map_iff A q (algebraMap P S x)).mp h3
    have h5 : x ∈ (q.comap (algebraMap P S)).primeCompl := h4
    have h6 : IsUnit (algebraMap P (Localization.AtPrime (q.comap (algebraMap P S))) x) :=
      IsLocalization.map_units _ ⟨x, h5⟩
    rw [← hx] at h6
    exact (IsUnit.mul_iff.mp h6).1
  exact ⟨isRegularLocalRing_of_flat_formallyUnramified
      (Localization.AtPrime (q.comap (algebraMap P S))) A,
    ringKrullDim_eq_of_flat_formallyUnramified
      (Localization.AtPrime (q.comap (algebraMap P S))) A⟩

/- English proof (translation)
The claim follows from `(isRegularLocalRing_and_ringKrullDim_eq_of_etale (CoordPolynomialRing k m) S (by intro p hp; exact isRegularLocalRing_localization_coordPolynomialRing k m p hp) q A).1`.
-/
theorem isRegularLocalRing_of_isLocalization_etale (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] (A : Type u) [CommRing A] [Algebra S A]
    [IsLocalization q.primeCompl A] :
    IsRegularLocalRing A :=
  (isRegularLocalRing_and_ringKrullDim_eq_of_etale (CoordPolynomialRing k m) S
    (by intro p hp; exact isRegularLocalRing_localization_coordPolynomialRing k m p hp) q A).1

/- English proof (translation)
The claim follows from `isRegularLocalRing_of_isLocalization_etale k m S q (Localization.AtPrime q)`.
-/
theorem isRegularLocalRing_localization_atPrime_etale (k : Type u) [Field k] (m : ℕ) (S : Type u)
    [CommRing S] [Algebra (CoordPolynomialRing k m) S] [Algebra.Etale (CoordPolynomialRing k m) S]
    (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) :=
  isRegularLocalRing_of_isLocalization_etale k m S q (Localization.AtPrime q)

end FunctorialResolution.EmbeddedResolution
