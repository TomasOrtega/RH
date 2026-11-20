import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteIntegralClosureOfIsIntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmoothOfIsDedekindDomain

namespace GlobalTheory.CurveNorm

/- English proof (translation)
Establish `hsurj : Function.Surjective e` using `fun c => ⟨algebraMap k E c, by simp⟩`. Use `haveI hp : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e`. Take `⟨Q, -, hQ, hQc⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (S := E') (RingHom.ker e) ⊥ (by`. Introduce `x hx`. Establish `: x = 0` using `hinj (by simpa using hx)`.

Simplify using `[this])`. Establish `key : ∀ x : E, algebraMap k (E' ⧸ Q) (e x) = Ideal.Quotient.mk Q (algebraMap E E' x)`. Introduce `x`. Establish `h1 : algebraMap k E (e x) - x ∈ RingHom.ker e` using `by simp [RingHom.mem_ker]`. Rewrite `h1` using `[← hQc, Ideal.mem_comap, map_sub, ← Ideal.Quotient.eq, ← IsScalarTower.algebraMap_apply]`.

Conclude with `h1`. Use `haveI : Algebra.IsIntegral k (E' ⧸ Q) := by`. Prove the components needed by the constructor for the conclusion. Introduce `y`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Take `⟨p, hpm, hp0⟩` from `Algebra.IsIntegral.isIntegral (R := E) y`. Use `⟨p.map (e : E →+* k), hpm.map _, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map]`. Establish `: (algebraMap k (E' ⧸ Q)).comp (e : E →+* k) = (Ideal.Quotient.mk Q).comp (algebraMap E E')` using `RingHom.ext key`. Rewrite using `[this, ← Polynomial.hom_eval₂, hp0, map_zero]`.

Establish `hbij : Function.Bijective (algebraMap k (E' ⧸ Q))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `φ : k ≃ₐ[k] (E' ⧸ Q)` to `AlgEquiv.ofBijective (Algebra.ofId k _) hbij`. Use `⟨(φ.symm : (E' ⧸ Q) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k Q), ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Apply `φ.injective` to reduce the goal to its premises.

Conclude with `(φ.apply_symm_apply _).trans (key x).symm`.
-/
theorem exists_lift_of_isIntegral {k E E' : Type} [Field k] [IsAlgClosed k] [CommRing E]
    [CommRing E'] [Algebra k E] [Algebra k E'] [Algebra E E'] [IsScalarTower k E E']
    [Algebra.IsIntegral E E'] (hinj : Function.Injective (algebraMap E E')) (e : E →ₐ[k] k) :
    ∃ e' : E' →ₐ[k] k, e'.comp (IsScalarTower.toAlgHom k E E') = e := by
  have hsurj : Function.Surjective e := fun c => ⟨algebraMap k E c, by simp⟩
  haveI hp : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := E')
    (RingHom.ker e) ⊥ (by
      intro x hx
      have : x = 0 := hinj (by simpa using hx)
      simp [this])
  have key : ∀ x : E, algebraMap k (E' ⧸ Q) (e x) = Ideal.Quotient.mk Q (algebraMap E E' x) := by
    intro x
    have h1 : algebraMap k E (e x) - x ∈ RingHom.ker e := by simp [RingHom.mem_ker]
    rw [← hQc, Ideal.mem_comap, map_sub, ← Ideal.Quotient.eq, ← IsScalarTower.algebraMap_apply] at h1
    exact h1
  haveI : Algebra.IsIntegral k (E' ⧸ Q) := by
    constructor
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨p, hpm, hp0⟩ := Algebra.IsIntegral.isIntegral (R := E) y
    refine ⟨p.map (e : E →+* k), hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have : (algebraMap k (E' ⧸ Q)).comp (e : E →+* k)
        = (Ideal.Quotient.mk Q).comp (algebraMap E E') := RingHom.ext key
    rw [this, ← Polynomial.hom_eval₂, hp0, map_zero]
  have hbij : Function.Bijective (algebraMap k (E' ⧸ Q)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let φ : k ≃ₐ[k] (E' ⧸ Q) := AlgEquiv.ofBijective (Algebra.ofId k _) hbij
  refine ⟨(φ.symm : (E' ⧸ Q) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k Q), ?_⟩
  ext x
  apply φ.injective
  exact (φ.apply_symm_apply _).trans (key x).symm

/- English proof (translation)
Set `F` to `FractionRing E`. Set `E' : Type` to `integralClosure E F`. Use `haveI : Module.Finite E E' := GlobalTheory.NormFin.finite_integralClosure_of_isAlgClosed ℂ E F`. Use `letI : Algebra ℂ E' := ((algebraMap E E').comp (algebraMap ℂ E)).toAlgebra`. Use `haveI : IsScalarTower ℂ E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Use `haveI : Algebra.FiniteType ℂ E' := Algebra.FiniteType.trans (S := E) inferInstance inferInstance`. Use `haveI : IsNoetherianRing E' := Algebra.FiniteType.isNoetherianRing ℂ E'`. Use `haveI : Ring.DimensionLEOne E' := Ring.DimensionLEOne.integralClosure E F`. Use `haveI : IsIntegrallyClosed E' := integralClosure.isIntegrallyClosedOfFiniteExtension F`. Use `haveI : IsDedekindRing E' := ⟨⟩`.

Use `haveI : IsDedekindDomain E' := inferInstance`. Establish `hinj : Function.Injective (algebraMap E E')`. Introduce `x y h`. Apply `IsFractionRing.injective E F` to reduce the goal to its premises. Conclude with `congrArg Subtype.val h`.

Take `⟨e', he'⟩` from `exists_lift_of_isIntegral hinj e`. Conclude with `⟨E', inferInstance, inferInstance, inferInstance, IsScalarTower.toAlgHom ℂ E E', e', GlobalTheory.DedekindSmooth.smooth_of_isDedekindDomain ℂ E', hinj, he'⟩`.
-/
theorem exists_smooth_normalisation (E : Type) [CommRing E] [IsDomain E] [Algebra ℂ E]
    [Algebra.FiniteType ℂ E] [Ring.DimensionLEOne E] (e : E →ₐ[ℂ] ℂ) :
    ∃ (E' : Type) (_ : CommRing E') (_ : IsDomain E') (_ : Algebra ℂ E') (ρ : E →ₐ[ℂ] E')
      (e' : E' →ₐ[ℂ] ℂ), Algebra.Smooth ℂ E' ∧ Function.Injective ρ ∧ e'.comp ρ = e := by
  let F := FractionRing E
  let E' : Type := integralClosure E F
  haveI : Module.Finite E E' := GlobalTheory.NormFin.finite_integralClosure_of_isAlgClosed ℂ E F
  letI : Algebra ℂ E' := ((algebraMap E E').comp (algebraMap ℂ E)).toAlgebra
  haveI : IsScalarTower ℂ E E' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType ℂ E' := Algebra.FiniteType.trans (S := E) inferInstance inferInstance
  haveI : IsNoetherianRing E' := Algebra.FiniteType.isNoetherianRing ℂ E'
  haveI : Ring.DimensionLEOne E' := Ring.DimensionLEOne.integralClosure E F
  haveI : IsIntegrallyClosed E' := integralClosure.isIntegrallyClosedOfFiniteExtension F
  haveI : IsDedekindRing E' := ⟨⟩
  haveI : IsDedekindDomain E' := inferInstance
  have hinj : Function.Injective (algebraMap E E') := by
    intro x y h
    apply IsFractionRing.injective E F
    exact congrArg Subtype.val h
  obtain ⟨e', he'⟩ := exists_lift_of_isIntegral hinj e
  exact ⟨E', inferInstance, inferInstance, inferInstance, IsScalarTower.toAlgHom ℂ E E', e',
    GlobalTheory.DedekindSmooth.smooth_of_isDedekindDomain ℂ E', hinj, he'⟩

end GlobalTheory.CurveNorm
