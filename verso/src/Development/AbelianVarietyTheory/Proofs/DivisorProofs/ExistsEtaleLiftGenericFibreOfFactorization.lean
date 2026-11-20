import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFibMapAlgebraMap
open CategoryTheory Limits

noncomputable section

namespace GlobalTheory.GenFibLift

open GlobalTheory.LocAcyc

/- English proof (translation)
The claim follows from `genFib_ringHom_ext (fun e => by simp only [RingHom.comp_apply, genFibMap_algebraMap, AlgHom.comp_apply])`.
-/
theorem genFibMap_comp {T E F O : Type} [CommRing T] [CommRing E] [CommRing F] [CommRing O]
    [Algebra T E] [Algebra T F] [Algebra T O] (φ : E →ₐ[T] F) (ψ : F →ₐ[T] O) :
    genFibMap (ψ.comp φ) = (genFibMap ψ).comp (genFibMap φ) :=
  genFib_ringHom_ext (fun e => by
    simp only [RingHom.comp_apply, genFibMap_algebraMap, AlgHom.comp_apply])

def den {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (t : nonZeroDivisors T) :
    Algebra.algebraMapSubmonoid O (nonZeroDivisors T) :=
  ⟨algebraMap T O t, Submonoid.mem_map_of_mem _ t.2⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem den_coe {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (t : nonZeroDivisors T) :
    ((den (O := O) t : Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) : O) = algebraMap T O t := rfl

/- English proof (translation)
Take `⟨⟨a, m⟩, rfl⟩` from `IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) x`. Take `⟨t, ht, hm⟩` from `Submonoid.mem_map.1 m.2`. Use `⟨a, ⟨t, ht⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[show m = den ⟨t, ht⟩ from Subtype.ext hm.symm]`.
-/
theorem exists_mk' {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (x : GenFib T O) :
    ∃ (a : O) (t : nonZeroDivisors T), x = IsLocalization.mk' (GenFib T O) a (den t) := by
  obtain ⟨⟨a, m⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)) x
  obtain ⟨t, ht, hm⟩ := Submonoid.mem_map.1 m.2
  refine ⟨a, ⟨t, ht⟩, ?_⟩
  rw [show m = den ⟨t, ht⟩ from Subtype.ext hm.symm]

/- English proof (translation)
Take `⟨c, hc⟩` from `(IsLocalization.mk'_eq_zero_iff a m).1 h`. Take `⟨t, ht, hct⟩` from `Submonoid.mem_map.1 c.2`. Conclude with `⟨⟨t, ht⟩, by simpa [hct] using hc⟩`.
-/
theorem exists_of_mk'_eq_zero {T O : Type} [CommRing T] [CommRing O] [Algebra T O] (a : O)
    (m : Algebra.algebraMapSubmonoid O (nonZeroDivisors T))
    (h : IsLocalization.mk' (GenFib T O) a m = 0) :
    ∃ t : nonZeroDivisors T, algebraMap T O t * a = 0 := by
  obtain ⟨c, hc⟩ := (IsLocalization.mk'_eq_zero_iff a m).1 h
  obtain ⟨t, ht, hct⟩ := Submonoid.mem_map.1 c.2
  exact ⟨⟨t, ht⟩, by simpa [hct] using hc⟩

/- English proof (translation)
Simplify using `only [genFibMap, IsLocalization.map_mk']`. Use `congr 1`. Use `ext`. Simplify using the standard rewrite rules.
-/
theorem genFibMap_mk' {T E O : Type} [CommRing T] [CommRing E] [CommRing O] [Algebra T E]
    [Algebra T O] (ψ : E →ₐ[T] O) (e : E) (t : nonZeroDivisors T) :
    genFibMap ψ (IsLocalization.mk' (GenFib T E) e (den t)) =
      IsLocalization.mk' (GenFib T O) (ψ e) (den t) := by
  simp only [genFibMap, IsLocalization.map_mk']
  congr 1
  ext
  simp

/- English proof (translation)
Use `haveI : Algebra.FinitePresentation ℤ U := Algebra.FinitePresentation.of_finiteType.mp inferInstance`. Take `⟨n, f, hf, s, hs⟩` from `Algebra.FinitePresentation.out (R := ℤ) (A := U)`. Use `choose a t ht using fun i : Fin n => exists_mk' (T := T) (u (f (MvPolynomial.X i)))`. Set `e : MvPolynomial (Fin n) R →ₐ[R] O` to `MvPolynomial.aeval a`. Set `θ : MvPolynomial (Fin n) ℤ →+* GenFib T (MvPolynomial (Fin n) R)` to `MvPolynomial.eval₂Hom (Int.castRingHom _) (fun i => IsLocalization.mk' _ (MvPolynomial.X i : MvPolynomial (Fin n) R) (den (t i)))`.

Establish `key : (genFibMap (e.restrictScalars T)).comp θ = u.comp f.toRingHom`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Conclude with `RingHom.congr_fun (RingHom.ext_int (((genFibMap (e.restrictScalars T)).comp θ).comp MvPolynomial.C) ((u.comp f.toRingHom).comp MvPolynomial.C)) r`. Introduce `i`.

Simplify using `only [RingHom.comp_apply, θ, MvPolynomial.eval₂Hom_X', genFibMap_mk']`. Rewrite using `[AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ht i]`. Simplify using `[e]`. Establish `hrel : ∀ r : s, ∃ (p : MvPolynomial (Fin n) R) (τ τ' : nonZeroDivisors T), θ r = IsLocalization.mk' _ p (den τ) ∧ e (algebraMap T _ τ' * p) = 0`. Introduce `r`.

Take `⟨p, τ, hp⟩` from `exists_mk' (T := T) (θ r)`. Establish `h0 : genFibMap (e.restrictScalars T) (θ r) = 0`. Establish `hr : (r : MvPolynomial (Fin n) ℤ) ∈ RingHom.ker f.toRingHom` using `hs ▸ Ideal.subset_span r.2`. Rewrite using `[← RingHom.comp_apply, key, RingHom.comp_apply, RingHom.mem_ker.1 hr, map_zero]`. Rewrite `h0` using `[hp, genFibMap_mk']`.

Take `⟨τ', hτ'⟩` from `exists_of_mk'_eq_zero _ _ h0`. Use `⟨p, τ, τ', hp, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← hτ']`. Simplify using `[IsScalarTower.algebraMap_apply T R (MvPolynomial (Fin n) R), IsScalarTower.algebraMap_apply T R O]`. Use `choose p τ τ' hθ he using hrel`.

Set `I : Ideal (MvPolynomial (Fin n) R)` to `Ideal.span (Set.range fun r : s => algebraMap T _ (τ' r : T) * p r)`. Establish `hIe : ∀ x ∈ I, e x = 0`. Introduce `x hx`. Establish `hle : I ≤ RingHom.ker e` using `Ideal.span_le.2 (by rintro _ ⟨r, rfl⟩; exact he r)`. Conclude with `hle hx`.

Use `haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) R) := Algebra.FinitePresentation.mvPolynomial R R (Fin n)`. Use `haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) R ⧸ I) := Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))`. Set `g : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] O` to `Ideal.Quotient.liftₐ I e hIe`. Set `q : MvPolynomial (Fin n) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I)` to `Ideal.Quotient.mkₐ R I`. Set `w0 : MvPolynomial (Fin n) ℤ →+* GenFib T (MvPolynomial (Fin n) R ⧸ I)` to `(genFibMap (q.restrictScalars T)).comp θ`.

Establish `hker : RingHom.ker f.toRingHom ≤ RingHom.ker w0`. Rewrite using `[← hs, Ideal.span_le]`. Introduce `r hr`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker]`. Simplify using `only [w0, RingHom.comp_apply]`.

Rewrite using `[hθ ⟨r, hr⟩, genFibMap_mk']`. Establish `hu : IsUnit (algebraMap (MvPolynomial (Fin n) R ⧸ I) (GenFib T (MvPolynomial (Fin n) R ⧸ I)) (algebraMap T _ (τ' ⟨r, hr⟩ : T)))` using `IsLocalization.map_units (M := Algebra.algebraMapSubmonoid _ (nonZeroDivisors T)) _ (den _)`. Use `(hu.mul_right_eq_zero).1 ?_` and prove the remaining obligations. Rewrite using `[← IsLocalization.mk'_one (M := Algebra.algebraMapSubmonoid _ (nonZeroDivisors T)), ← IsLocalization.mk'_mul, one_mul]`. Establish `hz : (q.restrictScalars T) (algebraMap T _ (τ' ⟨r, hr⟩ : T) * p ⟨r, hr⟩) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨⟨r, hr⟩, rfl⟩)`.

Rewrite `hz` using `[map_mul, AlgHom.commutes]`. Rewrite using `[hz, IsLocalization.mk'_zero]`. Use `⟨MvPolynomial (Fin n) R ⧸ I, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, g, RingHom.liftOfSurjective f.toRingHom hf ⟨w0, hker⟩, ?_⟩` and prove the remaining obligations. Apply `RingHom.ext` to reduce the goal to its premises. Introduce `x`.

Take `⟨y, rfl⟩` from `hf x`. Establish `hy : f y = f.toRingHom y` using `rfl`. Rewrite using `[RingHom.comp_apply, hy, RingHom.liftOfSurjective_comp_apply]`. Establish `hgq : (g.restrictScalars T).comp (q.restrictScalars T) = e.restrictScalars T`. Conclude with `AlgHom.ext fun x => AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp I e hIe) x`.

Establish `hcomp : (genFibMap (g.restrictScalars T)).comp w0 = u.comp f.toRingHom`. Simplify using `only [w0]`. Rewrite using `[← RingHom.comp_assoc, ← genFibMap_comp, hgq, key]`. Conclude with `RingHom.congr_fun hcomp y`.
-/
theorem exists_finitePresentation_lift (T R O : Type) [CommRing T] [CommRing R] [CommRing O]
    [Algebra T R] [Algebra R O] [Algebra T O] [IsScalarTower T R O]
    (U : Type) [CommRing U] [Algebra.FiniteType ℤ U] (u : U →+* GenFib T O) :
    ∃ (Z : Type) (_ : CommRing Z) (_ : Algebra R Z) (_ : Algebra T Z) (_ : IsScalarTower T R Z)
      (_ : Algebra.FinitePresentation R Z) (g : Z →ₐ[R] O) (w : U →+* GenFib T Z),
      (genFibMap (g.restrictScalars T)).comp w = u := by
  haveI : Algebra.FinitePresentation ℤ U := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨n, f, hf, s, hs⟩ := Algebra.FinitePresentation.out (R := ℤ) (A := U)

  choose a t ht using fun i : Fin n => exists_mk' (T := T) (u (f (MvPolynomial.X i)))
  let e : MvPolynomial (Fin n) R →ₐ[R] O := MvPolynomial.aeval a
  let θ : MvPolynomial (Fin n) ℤ →+* GenFib T (MvPolynomial (Fin n) R) :=
    MvPolynomial.eval₂Hom (Int.castRingHom _)
      (fun i => IsLocalization.mk' _ (MvPolynomial.X i : MvPolynomial (Fin n) R) (den (t i)))
  have key : (genFibMap (e.restrictScalars T)).comp θ = u.comp f.toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int
        (((genFibMap (e.restrictScalars T)).comp θ).comp MvPolynomial.C)
        ((u.comp f.toRingHom).comp MvPolynomial.C)) r
    · intro i
      simp only [RingHom.comp_apply, θ, MvPolynomial.eval₂Hom_X', genFibMap_mk']
      rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, ht i]
      simp [e]

  have hrel : ∀ r : s, ∃ (p : MvPolynomial (Fin n) R) (τ τ' : nonZeroDivisors T),
      θ r = IsLocalization.mk' _ p (den τ) ∧ e (algebraMap T _ τ' * p) = 0 := by
    intro r
    obtain ⟨p, τ, hp⟩ := exists_mk' (T := T) (θ r)
    have h0 : genFibMap (e.restrictScalars T) (θ r) = 0 := by
      have hr : (r : MvPolynomial (Fin n) ℤ) ∈ RingHom.ker f.toRingHom := hs ▸ Ideal.subset_span r.2
      rw [← RingHom.comp_apply, key, RingHom.comp_apply, RingHom.mem_ker.1 hr, map_zero]
    rw [hp, genFibMap_mk'] at h0
    obtain ⟨τ', hτ'⟩ := exists_of_mk'_eq_zero _ _ h0
    refine ⟨p, τ, τ', hp, ?_⟩
    rw [map_mul, ← hτ']
    simp [IsScalarTower.algebraMap_apply T R (MvPolynomial (Fin n) R),
      IsScalarTower.algebraMap_apply T R O]
  choose p τ τ' hθ he using hrel
  let I : Ideal (MvPolynomial (Fin n) R) :=
    Ideal.span (Set.range fun r : s => algebraMap T _ (τ' r : T) * p r)
  have hIe : ∀ x ∈ I, e x = 0 := by
    intro x hx
    have hle : I ≤ RingHom.ker e := Ideal.span_le.2 (by rintro _ ⟨r, rfl⟩; exact he r)
    exact hle hx
  haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) R) :=
    Algebra.FinitePresentation.mvPolynomial R R (Fin n)
  haveI : Algebra.FinitePresentation R (MvPolynomial (Fin n) R ⧸ I) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))
  let g : (MvPolynomial (Fin n) R ⧸ I) →ₐ[R] O := Ideal.Quotient.liftₐ I e hIe
  let q : MvPolynomial (Fin n) R →ₐ[R] (MvPolynomial (Fin n) R ⧸ I) := Ideal.Quotient.mkₐ R I
  let w0 : MvPolynomial (Fin n) ℤ →+* GenFib T (MvPolynomial (Fin n) R ⧸ I) :=
    (genFibMap (q.restrictScalars T)).comp θ
  have hker : RingHom.ker f.toRingHom ≤ RingHom.ker w0 := by
    rw [← hs, Ideal.span_le]
    intro r hr
    rw [SetLike.mem_coe, RingHom.mem_ker]
    simp only [w0, RingHom.comp_apply]
    rw [hθ ⟨r, hr⟩, genFibMap_mk']
    have hu : IsUnit (algebraMap (MvPolynomial (Fin n) R ⧸ I) (GenFib T (MvPolynomial (Fin n) R ⧸ I))
        (algebraMap T _ (τ' ⟨r, hr⟩ : T))) :=
      IsLocalization.map_units (M := Algebra.algebraMapSubmonoid _ (nonZeroDivisors T)) _ (den _)
    refine (hu.mul_right_eq_zero).1 ?_
    rw [← IsLocalization.mk'_one (M := Algebra.algebraMapSubmonoid _ (nonZeroDivisors T)),
      ← IsLocalization.mk'_mul, one_mul]
    have hz : (q.restrictScalars T) (algebraMap T _ (τ' ⟨r, hr⟩ : T) * p ⟨r, hr⟩) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨⟨r, hr⟩, rfl⟩)
    rw [map_mul, AlgHom.commutes] at hz
    rw [hz, IsLocalization.mk'_zero]

  refine ⟨MvPolynomial (Fin n) R ⧸ I, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, g, RingHom.liftOfSurjective f.toRingHom hf ⟨w0, hker⟩, ?_⟩
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := hf x
  have hy : f y = f.toRingHom y := rfl
  rw [RingHom.comp_apply, hy, RingHom.liftOfSurjective_comp_apply]
  have hgq : (g.restrictScalars T).comp (q.restrictScalars T) = e.restrictScalars T := by
    exact AlgHom.ext fun x => AlgHom.congr_fun (Ideal.Quotient.liftₐ_comp I e hIe) x
  have hcomp : (genFibMap (g.restrictScalars T)).comp w0 = u.comp f.toRingHom := by
    simp only [w0]
    rw [← RingHom.comp_assoc, ← genFibMap_comp, hgq, key]
  exact RingHom.congr_fun hcomp y

/- English proof (translation)
Introduce `T R O _ _ _ _ _ _ _ H U _ _ u`. Take `⟨Z, _, _, _, _, _, g, w, hw⟩` from `exists_finitePresentation_lift T R O U u`. Take `⟨W, _, _, _, u0, v, hv⟩` from `H Z g`. Use `letI : Algebra T W := ((algebraMap R W).comp (algebraMap T R)).toAlgebra`. Use `haveI hTRW : IsScalarTower T R W := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.

Use `⟨W, inferInstance, inferInstance, inferInstance, hTRW, inferInstance, v, (genFibMap (u0.restrictScalars T)).comp w, ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.comp_assoc, ← genFibMap_comp]`. Establish `hvu : (v.restrictScalars T).comp (u0.restrictScalars T) = g.restrictScalars T` using `AlgHom.ext fun z => AlgHom.congr_fun hv z`. Rewrite using `[hvu, hw]`.
-/
theorem exists_etale_genFib_lift : ∀ (T R O : Type) [CommRing T] [CommRing R] [CommRing O]
    [Algebra T R] [Algebra R O] [Algebra T O] [IsScalarTower T R O],
    (∀ (Z : Type) [CommRing Z] [Algebra R Z] [Algebra.FinitePresentation R Z] (g : Z →ₐ[R] O),
      ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra.Etale R W)
        (u : Z →ₐ[R] W) (v : W →ₐ[R] O), v.comp u = g) →
    ∀ (U : Type) [CommRing U] [Algebra.FiniteType ℤ U] (u : U →+* GlobalTheory.LocAcyc.GenFib T O),
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra R W) (_ : Algebra T W) (_ : IsScalarTower T R W)
      (_ : Algebra.Etale R W) (ψ : W →ₐ[R] O) (uW : U →+* GlobalTheory.LocAcyc.GenFib T W),
      (GlobalTheory.LocAcyc.genFibMap (ψ.restrictScalars T)).comp uW = u := by
  intro T R O _ _ _ _ _ _ _ H U _ _ u
  obtain ⟨Z, _, _, _, _, _, g, w, hw⟩ := exists_finitePresentation_lift T R O U u
  obtain ⟨W, _, _, _, u0, v, hv⟩ := H Z g
  letI : Algebra T W := ((algebraMap R W).comp (algebraMap T R)).toAlgebra
  haveI hTRW : IsScalarTower T R W := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨W, inferInstance, inferInstance, inferInstance, hTRW, inferInstance, v,
    (genFibMap (u0.restrictScalars T)).comp w, ?_⟩
  rw [← RingHom.comp_assoc, ← genFibMap_comp]
  have hvu : (v.restrictScalars T).comp (u0.restrictScalars T) = g.restrictScalars T :=
    AlgHom.ext fun z => AlgHom.congr_fun hv z
  rw [hvu, hw]

end GlobalTheory.GenFibLift
