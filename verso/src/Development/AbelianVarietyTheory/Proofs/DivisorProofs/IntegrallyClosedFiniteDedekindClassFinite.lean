import Mathlib

namespace GlobalTheory.IntClosedOrder

/- English proof (translation)
Use `haveI : @IsScalarTower ℤ ℚ (FractionRing A) Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.of_algebraMap_eq (fun x => by`. Rewrite using `[eq_intCast (algebraMap ℤ ℚ), map_intCast, eq_intCast])`. Use `haveI : FiniteDimensional ℚ (FractionRing A) := Module.Finite.of_isLocalization ℤ A (nonZeroDivisors ℤ)`. Conclude with `{}`.
-/
theorem numberField_fractionRing (A : Type) [CommRing A] [IsDomain A] [CharZero A]
    [Module.Finite ℤ A] : NumberField (FractionRing A) := by
  haveI : @IsScalarTower ℤ ℚ (FractionRing A) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [eq_intCast (algebraMap ℤ ℚ), map_intCast, eq_intCast])
  haveI : FiniteDimensional ℚ (FractionRing A) :=
    Module.Finite.of_isLocalization ℤ A (nonZeroDivisors ℤ)
  exact {}

/- English proof (translation)
Use `haveI : Algebra.IsIntegral ℤ A := Algebra.IsIntegral.of_finite ℤ A`. Use `⟨IsFractionRing.injective A (FractionRing A), fun {x} => ⟨fun hx => ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `(IsIntegrallyClosed.isIntegral_iff (R := A) (K := FractionRing A)).mp (IsIntegral.tower_top (A := A) hx)`. Introduce and unpack `⟨a, rfl⟩`. Conclude with `(Algebra.IsIntegral.isIntegral (R := ℤ) a).algebraMap`.
-/
theorem isIntegralClosure_int (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Module.Finite ℤ A] : IsIntegralClosure A ℤ (FractionRing A) := by
  haveI : Algebra.IsIntegral ℤ A := Algebra.IsIntegral.of_finite ℤ A
  refine ⟨IsFractionRing.injective A (FractionRing A), fun {x} => ⟨fun hx => ?_, ?_⟩⟩
  · exact (IsIntegrallyClosed.isIntegral_iff (R := A) (K := FractionRing A)).mp
      (IsIntegral.tower_top (A := A) hx)
  · rintro ⟨a, rfl⟩
    exact (Algebra.IsIntegral.isIntegral (R := ℤ) a).algebraMap

/- English proof (translation)
Introduce `A _ _ _ _ _`. Use `haveI := numberField_fractionRing A`. Use `haveI := isIntegralClosure_int A`. Use `haveI : @IsScalarTower ℤ ℚ (FractionRing A) Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.of_algebraMap_eq (fun x => by`. Rewrite using `[eq_intCast (algebraMap ℤ ℚ), map_intCast, eq_intCast])`.

Use `⟨IsIntegralClosure.isDedekindDomain ℤ ℚ (FractionRing A) A, ?_⟩` and prove the remaining obligations. Use `letI := ClassGroup.fintypeOfAdmissibleOfFinite ℚ (FractionRing A) AbsoluteValue.absIsAdmissible (S := A)`. Conclude with `Finite.of_fintype _`.
-/
theorem isDedekindDomain_and_finite_classGroup : ∀ (A : Type) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CharZero A] [Module.Finite ℤ A],
    IsDedekindDomain A ∧ Finite (ClassGroup A) := by
  intro A _ _ _ _ _
  haveI := numberField_fractionRing A
  haveI := isIntegralClosure_int A
  haveI : @IsScalarTower ℤ ℚ (FractionRing A) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [eq_intCast (algebraMap ℤ ℚ), map_intCast, eq_intCast])
  refine ⟨IsIntegralClosure.isDedekindDomain ℤ ℚ (FractionRing A) A, ?_⟩
  letI := ClassGroup.fintypeOfAdmissibleOfFinite ℚ (FractionRing A) AbsoluteValue.absIsAdmissible
    (S := A)
  exact Finite.of_fintype _

end GlobalTheory.IntClosedOrder
