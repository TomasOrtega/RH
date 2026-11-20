import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SmoothStalkNormal

/- English proof (translation)
Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)`. Rewrite using `[← hU.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk]`. Establish `: Flat (Spec.map (X.presheaf.germ U x hx))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @Flat)]`. Set `_` to `X.presheaf.algebra_section_stalk ⟨x, hx⟩`.

Use `hU.isLocalization_stalk ⟨x, hx⟩` as an intermediate fact. Conclude with `IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl`. Use `infer_instance`.
-/
theorem flat_fromSpecStalk' (X : Scheme.{0}) (x : X) : Flat (X.fromSpecStalk x) := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx, IsAffineOpen.fromSpecStalk]
  have : Flat (Spec.map (X.presheaf.germ U x hx)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
    have := hU.isLocalization_stalk ⟨x, hx⟩
    exact IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
  infer_instance

/- English proof (translation)
Use `algebraize [f]`. Use `(injective_iff_map_eq_zero f).2 fun r hr => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Establish `hreg : IsSMulRegular B r` using `Module.Flat.isSMulRegular_of_isRegular (isRegular_of_ne_zero h0)`. Establish `h1 : r • (1 : B) = r • (0 : B)`.

Rewrite using `[smul_zero, Algebra.smul_def, _root_.mul_one]`. Conclude with `hr`. Conclude with `one_ne_zero (hreg h1)`.
-/
theorem injective_of_flat_of_isDomain {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Nontrivial B] (f : A →+* B) (hf : f.Flat) : Function.Injective f := by
  algebraize [f]
  refine (injective_iff_map_eq_zero f).2 fun r hr => ?_
  by_contra h0
  have hreg : IsSMulRegular B r :=
    Module.Flat.isSMulRegular_of_isRegular (isRegular_of_ne_zero h0)
  have h1 : r • (1 : B) = r • (0 : B) := by
    rw [smul_zero, Algebra.smul_def, _root_.mul_one]; exact hr
  exact one_ne_zero (hreg h1)

/- English proof (translation)
Introduce `R _ _ X p hp x`. Use `haveI : Smooth p := hp`. Use `haveI : IsRegularRing (CommRingCat.of R) := GlobalTheory.isRegularRing_of_isRegularLocalRing R`. Establish `hreg : IsRegularLocalRing (X.presheaf.stalk x)` using `GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth p x`. Take `⟨hdom, hint⟩` from `GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (X.presheaf.stalk x)`.

Establish `hRdom : IsDomain R` using `(GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).1`. Establish `hfl : (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat` using `by haveI := flat_fromSpecStalk' X x`. Establish `h : Flat (Spec.map (Spec.preimage (X.fromSpecStalk x ≫ p)))`. Rewrite using `[Spec.map_preimage]`. Use `infer_instance`.

Conclude with `(HasRingHomProperty.Spec_iff (P := @Flat)).1 h`. Use `⟨hdom, inferInstance, hint, hfl, ?_⟩` and prove the remaining obligations. Conclude with `injective_of_flat_of_isDomain (A := R) _ hfl`.
-/
theorem stalk_of_smooth_over_regular :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (X : Scheme.{0}) (p : X ⟶ Sp R), Smooth p →
      ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsNoetherianRing (X.presheaf.stalk x) ∧
        IsIntegrallyClosed (X.presheaf.stalk x) ∧
        (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat ∧
        Function.Injective (Spec.preimage (X.fromSpecStalk x ≫ p)).hom := by
  intro R _ _ X p hp x
  haveI : Smooth p := hp
  haveI : IsRegularRing (CommRingCat.of R) := GlobalTheory.isRegularRing_of_isRegularLocalRing R
  have hreg : IsRegularLocalRing (X.presheaf.stalk x) :=
    GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth p x
  obtain ⟨hdom, hint⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing (X.presheaf.stalk x)
  have hRdom : IsDomain R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).1
  have hfl : (Spec.preimage (X.fromSpecStalk x ≫ p)).hom.Flat := by
    haveI := flat_fromSpecStalk' X x
    have h : Flat (Spec.map (Spec.preimage (X.fromSpecStalk x ≫ p))) := by
      rw [Spec.map_preimage]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Flat)).1 h
  refine ⟨hdom, inferInstance, hint, hfl, ?_⟩
  exact injective_of_flat_of_isDomain (A := R) _ hfl

end GlobalTheory.SmoothStalkNormal
