import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

/- English proof (translation)
Introduce `A R _ _ _ _ _ _ _ hinj D _ _ _ _`. Use `letI := closureAlg A R D`. Set `M : Submonoid R` to `Algebra.algebraMapSubmonoid R (nonZeroDivisors A)`. Establish `hM : M ≤ nonZeroDivisors R`. Introduce and unpack `_ ⟨a, ha, rfl⟩`.

Use `mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero ha ?_` and prove the remaining obligations. Conclude with `hinj (h.trans (map_zero _).symm)`. Use `haveI : IsDomain (GlobalTheory.LocAcyc.GenFib A R) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM`. Use `haveI : IsIntegrallyClosed (GlobalTheory.LocAcyc.GenFib A R) := isIntegrallyClosed_of_isLocalization (GlobalTheory.LocAcyc.GenFib A R) M hM`. Establish `hRGF : Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R))` using `IsLocalization.injective (GlobalTheory.LocAcyc.GenFib A R) hM`.

Establish `h1 : IsIntegrallyClosedIn D (D ⊗[GlobalTheory.LocAcyc.GenFib A R] FractionRing (GlobalTheory.LocAcyc.GenFib A R))` using `GlobalTheory.isIntegrallyClosedIn_tensor_of_smooth`. Take `⟨hDinj, hDcl⟩` from `isIntegrallyClosedIn_iff.mp h1`. Set `g : closure A R D →+* D ⊗[GlobalTheory.LocAcyc.GenFib A R] FractionRing (GlobalTheory.LocAcyc.GenFib A R)` to `(algebraMap D _).comp (closure A R D).subtype`. Establish `hg : Function.Injective g` using `hDinj.comp Subtype.val_injective`. Establish `hunit : ∀ n : Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R), IsUnit (g n)`.

Introduce and unpack `⟨_, s, hs, rfl⟩`. Establish `hs0 : algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s ≠ 0`. Introduce `h`. Conclude with `nonZeroDivisors.ne_zero hs (hRGF (h.trans (map_zero _).symm))`. Establish `hL : IsUnit (algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing (GlobalTheory.LocAcyc.GenFib A R)) (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s))` using `((IsFractionRing.injective (GlobalTheory.LocAcyc.GenFib A R) _).ne_iff' (map_zero _)).mpr hs0 |>.isUnit`.

Establish `heq : g (algebraMap R (closure A R D) s) = Algebra.TensorProduct.includeRight (algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing (GlobalTheory.LocAcyc.GenFib A R)) (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s))`. Rewrite using `[Algebra.TensorProduct.includeRight.commutes]`. Both sides reduce to the same expression. Rewrite using `[heq]`. Conclude with `hL.map _`.

Set `φ` to `IsLocalization.lift (M := Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R)) (S := Localization (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))) hunit`. Establish `hφ : φ.comp (algebraMap (closure A R D) _) = g` using `IsLocalization.lift_comp _`. Establish `hφinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`.

Take `⟨⟨c, n⟩, rfl⟩` from `IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R)) z`. Establish `hc : g c = 0`. Use `(IsLocalization.lift_mk'_spec (M := Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R)) (S := Localization (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))) (hg := hunit) c 0 n).mp hz` as an intermediate fact. Rewrite `this` using `[mul_zero]`. Conclude with `this`.

Establish `: c = 0` using `hg (hc.trans (map_zero g).symm)`. Simplify using `only [this, IsLocalization.mk'_zero]`. Use `isIntegrallyClosedIn_iff.mpr ⟨?_, fun {x} hx => ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Apply `hg` to reduce the goal to its premises.

Rewrite using `[← hφ, RingHom.comp_apply, RingHom.comp_apply, hab]`. Take `⟨p, hp, hpx⟩` from `hx`. Establish `hev : Polynomial.eval₂ g (φ x) p = 0`. Use `Polynomial.hom_eval₂ p (algebraMap (closure A R D) _) φ x` as an intermediate fact. Rewrite `this` using `[hpx, map_zero, hφ]`.

Conclude with `this.symm`. Establish `hxD : IsIntegral D (φ x)`. Use `⟨p.map (closure A R D).subtype, hp.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Conclude with `hev`.

Take `⟨d, hd⟩` from `hDcl hxD`. Establish `hdC : Polynomial.eval₂ (closure A R D).subtype d p = 0`. Apply `hDinj` to reduce the goal to its premises. Rewrite using `[Polynomial.hom_eval₂, hd, map_zero]`. Conclude with `hev`.

Establish `hdmem : d ∈ closure A R D`. Use `letI : Algebra R D := (baseHom A R D).toAlgebra`. Use `letI : Algebra (closure A R D) D := (closure A R D).subtype.toAlgebra`. Use `haveI : IsScalarTower R (closure A R D) D := .of_algebraMap_eq fun _ => rfl`. Use `haveI : Algebra.IsIntegral R (closure A R D) := ⟨fun c => by`.

Set `f : closure A R D →ₐ[R] D` to `{ (closure A R D).subtype with commutes' := fun _ => rfl }`. Conclude with `(isIntegral_algHom_iff f Subtype.val_injective).mp c.2⟩`. Establish `hxC : IsIntegral (closure A R D) d` using `⟨p, hp, hdC⟩`. Conclude with `isIntegral_trans _ hxC`. Use `⟨⟨d, hdmem⟩, hφinj ?_⟩` and prove the remaining obligations.

Rewrite using `[← RingHom.comp_apply, hφ]`. Conclude with `hd`.
-/
theorem isIntegrallyClosedIn_closure_localization : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra A R], Function.Injective (algebraMap A R) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    IsIntegrallyClosedIn (GlobalTheory.KeyOriginNoeth.closure A R D)
      (Localization (Algebra.algebraMapSubmonoid (GlobalTheory.KeyOriginNoeth.closure A R D)
        (nonZeroDivisors R))) := by
  intro A R _ _ _ _ _ _ _ hinj D _ _ _ _
  letI := closureAlg A R D
  let M : Submonoid R := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  have hM : M ≤ nonZeroDivisors R := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero ha ?_
    exact hinj (h.trans (map_zero _).symm)
  haveI : IsDomain (GlobalTheory.LocAcyc.GenFib A R) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  haveI : IsIntegrallyClosed (GlobalTheory.LocAcyc.GenFib A R) :=
    isIntegrallyClosed_of_isLocalization (GlobalTheory.LocAcyc.GenFib A R) M hM
  have hRGF : Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) :=
    IsLocalization.injective (GlobalTheory.LocAcyc.GenFib A R) hM
  have h1 : IsIntegrallyClosedIn D (D ⊗[GlobalTheory.LocAcyc.GenFib A R] FractionRing (GlobalTheory.LocAcyc.GenFib A R)) :=
    GlobalTheory.isIntegrallyClosedIn_tensor_of_smooth
  obtain ⟨hDinj, hDcl⟩ := isIntegrallyClosedIn_iff.mp h1
  let g : closure A R D →+* D ⊗[GlobalTheory.LocAcyc.GenFib A R] FractionRing (GlobalTheory.LocAcyc.GenFib A R) :=
    (algebraMap D _).comp (closure A R D).subtype
  have hg : Function.Injective g := hDinj.comp Subtype.val_injective
  have hunit : ∀ n : Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R), IsUnit (g n) := by
    rintro ⟨_, s, hs, rfl⟩
    have hs0 : algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s ≠ 0 := by
      intro h
      exact nonZeroDivisors.ne_zero hs (hRGF (h.trans (map_zero _).symm))
    have hL : IsUnit (algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing (GlobalTheory.LocAcyc.GenFib A R))
        (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s)) :=
      ((IsFractionRing.injective (GlobalTheory.LocAcyc.GenFib A R) _).ne_iff' (map_zero _)).mpr hs0 |>.isUnit
    have heq : g (algebraMap R (closure A R D) s) = Algebra.TensorProduct.includeRight
        (algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing (GlobalTheory.LocAcyc.GenFib A R))
          (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s)) := by
      rw [Algebra.TensorProduct.includeRight.commutes]
      rfl
    rw [heq]
    exact hL.map _
  let φ := IsLocalization.lift (M := Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))
    (S := Localization (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))) hunit
  have hφ : φ.comp (algebraMap (closure A R D) _) = g := IsLocalization.lift_comp _

  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨c, n⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R)) z
    have hc : g c = 0 := by
      have := (IsLocalization.lift_mk'_spec (M := Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))
        (S := Localization (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))) (hg := hunit) c 0 n).mp hz
      rw [mul_zero] at this
      exact this
    have : c = 0 := hg (hc.trans (map_zero g).symm)
    simp only [this, IsLocalization.mk'_zero]
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, fun {x} hx => ?_⟩
  · intro a b hab
    apply hg
    rw [← hφ, RingHom.comp_apply, RingHom.comp_apply, hab]
  · obtain ⟨p, hp, hpx⟩ := hx
    have hev : Polynomial.eval₂ g (φ x) p = 0 := by
      have := Polynomial.hom_eval₂ p (algebraMap (closure A R D) _) φ x
      rw [hpx, map_zero, hφ] at this
      exact this.symm
    have hxD : IsIntegral D (φ x) := by
      refine ⟨p.map (closure A R D).subtype, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hev
    obtain ⟨d, hd⟩ := hDcl hxD

    have hdC : Polynomial.eval₂ (closure A R D).subtype d p = 0 := by
      apply hDinj
      rw [Polynomial.hom_eval₂, hd, map_zero]
      exact hev
    have hdmem : d ∈ closure A R D := by
      letI : Algebra R D := (baseHom A R D).toAlgebra
      letI : Algebra (closure A R D) D := (closure A R D).subtype.toAlgebra
      haveI : IsScalarTower R (closure A R D) D := .of_algebraMap_eq fun _ => rfl
      haveI : Algebra.IsIntegral R (closure A R D) := ⟨fun c => by
        let f : closure A R D →ₐ[R] D := { (closure A R D).subtype with commutes' := fun _ => rfl }
        exact (isIntegral_algHom_iff f Subtype.val_injective).mp c.2⟩
      have hxC : IsIntegral (closure A R D) d := ⟨p, hp, hdC⟩
      exact isIntegral_trans _ hxC
    refine ⟨⟨d, hdmem⟩, hφinj ?_⟩
    rw [← RingHom.comp_apply, hφ]
    exact hd

end GlobalTheory.KeyOriginNoeth
