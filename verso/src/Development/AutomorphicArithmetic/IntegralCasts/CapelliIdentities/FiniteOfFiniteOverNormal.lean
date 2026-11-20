import Mathlib

namespace UpperTheory

open nonZeroDivisors

/- English proof (translation)
Use `letI : Algebra P K := ((algebraMap A K).comp (algebraMap P A)).toAlgebra`. Use `haveI : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr ((IsFractionRing.injective A K).comp (FaithfulSMul.algebraMap_injective P A))`. Use `letI : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K`. Use `haveI : IsScalarTower P (FractionRing P) K := FractionRing.isScalarTower_liftAlgebra P K`.

Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid A P⁰) K := inferInstance`. Use `haveI : FiniteDimensional (FractionRing P) K := Module.Finite.of_isLocalization P A P⁰`. Use `haveI : CharZero (FractionRing P) := IsFractionRing.charZero P`. Use `haveI : Algebra.IsSeparable (FractionRing P) K := inferInstance`. Use `haveI : IsIntegralClosure (integralClosure A K) P K := ⟨Subtype.val_injective, fun {x} => ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ isIntegral_trans _ y.2⟩⟩`.

Use `haveI : Module.Finite P (integralClosure A K) := IsIntegralClosure.finite P (FractionRing P) K (integralClosure A K)`. Conclude with `Module.Finite.of_restrictScalars_finite P A (integralClosure A K)`.
-/
private theorem finite_of_finite_over_normal (P A K : Type*) [CommRing P] [IsDomain P]
    [CharZero P] [IsIntegrallyClosed P] [IsNoetherianRing P] [CommRing A] [IsDomain A]
    [Algebra P A] [FaithfulSMul P A] [Module.Finite P A] [Field K] [Algebra A K]
    [IsFractionRing A K] : Module.Finite A (integralClosure A K) := by
  letI : Algebra P K := ((algebraMap A K).comp (algebraMap P A)).toAlgebra
  haveI : IsScalarTower P A K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr
    ((IsFractionRing.injective A K).comp (FaithfulSMul.algebraMap_injective P A))
  letI : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  haveI : IsScalarTower P (FractionRing P) K := FractionRing.isScalarTower_liftAlgebra P K
  haveI : IsLocalization (Algebra.algebraMapSubmonoid A P⁰) K := inferInstance
  haveI : FiniteDimensional (FractionRing P) K := Module.Finite.of_isLocalization P A P⁰
  haveI : CharZero (FractionRing P) := IsFractionRing.charZero P
  haveI : Algebra.IsSeparable (FractionRing P) K := inferInstance
  haveI : IsIntegralClosure (integralClosure A K) P K :=
    ⟨Subtype.val_injective, fun {x} =>
      ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ isIntegral_trans _ y.2⟩⟩
  haveI : Module.Finite P (integralClosure A K) :=
    IsIntegralClosure.finite P (FractionRing P) K (integralClosure A K)
  exact Module.Finite.of_restrictScalars_finite P A (integralClosure A K)

/- English proof (translation)
Take `⟨s, g, hinj, hfin⟩` from `exists_finite_inj_algHom_of_fg k A`. Use `letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra`. Use `haveI : Module.Finite (MvPolynomial (Fin s) k) A := hfin`. Use `haveI : FaithfulSMul (MvPolynomial (Fin s) k) A := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj`. Conclude with `finite_of_finite_over_normal (MvPolynomial (Fin s) k) A K`.
-/
theorem integralClosure_finite (k A K : Type*) [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [Field K] [Algebra A K] [IsFractionRing A K] :
    Module.Finite A (integralClosure A K) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  letI : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
  haveI : Module.Finite (MvPolynomial (Fin s) k) A := hfin
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact finite_of_finite_over_normal (MvPolynomial (Fin s) k) A K

end UpperTheory
