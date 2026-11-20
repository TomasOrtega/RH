import Mathlib

namespace GlobalTheory.IntegralInValuationSubring

/- English proof (translation)
Set `f : R →+* A` to `(algebraMap R Ω).codRestrict A h`. Use `letI : Algebra R A := f.toAlgebra`. Use `haveI : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Establish `hA : IsIntegral A b` using `hb.tower_top`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 hA`.

Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_valuationSubring_of_isIntegral {Ω : Type} [Field Ω] {R : Type} [CommRing R]
    [Algebra R Ω] (A : ValuationSubring Ω) (h : ∀ r : R, algebraMap R Ω r ∈ A) {b : Ω}
    (hb : IsIntegral R b) : b ∈ A := by
  let f : R →+* A := (algebraMap R Ω).codRestrict A h
  letI : Algebra R A := f.toAlgebra
  haveI : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hA : IsIntegral A b := hb.tower_top
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := Ω)).1 hA
  rw [← hy]
  exact y.2

end GlobalTheory.IntegralInValuationSubring
