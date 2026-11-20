import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MaxPt

/- English proof (translation)
Introduce `X p _ U hU m hm`. Establish `h1` using `LocallyOfFiniteType.finiteType_of_affine_subset p (isAffineOpen_top (Sp ℂ)) hU (by simp)`. Establish `h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType` using `RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective`. Establish `hft : (algX p U).FiniteType` using `h1.comp h2`. Use `letI : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra`.

Use `haveI : Algebra.FiniteType ℂ Γ(X, U) := hft`. Use `haveI : m.IsMaximal := hm`. Use `letI : Field (Γ(X, U) ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Module.Finite ℂ (Γ(X, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(X, U) ⧸ m)`. Establish `hbij : Function.Bijective (algebraMap ℂ (Γ(X, U) ⧸ m))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`.

Set `e : ℂ ≃+* (Γ(X, U) ⧸ m)` to `RingEquiv.ofBijective _ hbij`. Set `φ : Γ(X, U) →+* ℂ` to `(e.symm : (Γ(X, U) ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m)`. Establish `hφ : ∀ a, φ (algX p U a) = (RingHom.id ℂ) a`. Introduce `a`. Use `show e.symm (Ideal.Quotient.mk m (algebraMap ℂ Γ(X, U) a)) = a`.

Rewrite using `[← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]`. Conclude with `e.symm_apply_apply a`. Use `⟨CxPts.ofHom hU φ hφ, CxPts.ofHom_mem hU φ hφ, ?_⟩` and prove the remaining obligations. Establish `hev : CxPts.evHom (CxPts.ofHom_mem hU φ hφ) = φ`. Use extensionality with `f`.

Rewrite using `[← CxPts.ev_eq, CxPts.ev_ofHom]`. Rewrite using `[hev]`. Use extensionality with `f`. Rewrite using `[RingHom.mem_ker]`. Use `show f ∈ m ↔ e.symm (Ideal.Quotient.mk m f) = 0`.

Rewrite using `[RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem exists_cxPts_ker_eq : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) [LocallyOfFiniteType p] (U : X.Opens), IsAffineOpen U →
    ∀ m : Ideal Γ(X, U), m.IsMaximal → ∃ (y : CxPts p (RingHom.id ℂ)) (hy : y ∈ CxPts.ptsIn p (RingHom.id ℂ) U),
      m = RingHom.ker (CxPts.evHom hy) := by
  intro X p _ U hU m hm
  have h1 := LocallyOfFiniteType.finiteType_of_affine_subset p (isAffineOpen_top (Sp ℂ)) hU (by simp)
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.symm.surjective
  have hft : (algX p U).FiniteType := h1.comp h2
  letI : Algebra ℂ Γ(X, U) := (algX p U).toAlgebra
  haveI : Algebra.FiniteType ℂ Γ(X, U) := hft
  haveI : m.IsMaximal := hm
  letI : Field (Γ(X, U) ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite ℂ (Γ(X, U) ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℂ (Γ(X, U) ⧸ m)
  have hbij : Function.Bijective (algebraMap ℂ (Γ(X, U) ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : ℂ ≃+* (Γ(X, U) ⧸ m) := RingEquiv.ofBijective _ hbij
  let φ : Γ(X, U) →+* ℂ := (e.symm : (Γ(X, U) ⧸ m) →+* ℂ).comp (Ideal.Quotient.mk m)
  have hφ : ∀ a, φ (algX p U a) = (RingHom.id ℂ) a := by
    intro a
    show e.symm (Ideal.Quotient.mk m (algebraMap ℂ Γ(X, U) a)) = a
    rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    exact e.symm_apply_apply a
  refine ⟨CxPts.ofHom hU φ hφ, CxPts.ofHom_mem hU φ hφ, ?_⟩
  have hev : CxPts.evHom (CxPts.ofHom_mem hU φ hφ) = φ := by
    ext f
    rw [← CxPts.ev_eq, CxPts.ev_ofHom]
  rw [hev]
  ext f
  rw [RingHom.mem_ker]
  show f ∈ m ↔ e.symm (Ideal.Quotient.mk m f) = 0
  rw [RingEquiv.symm_apply_eq, map_zero, Ideal.Quotient.eq_zero_iff_mem]

end GlobalTheory.MaxPt
