import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfValNonneg

noncomputable section

namespace GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma Polynomial

/- English proof (translation)
Introduce `hd`. Establish `h1 : Nat.card (IsLocalRing.ResidueField K'.O) = 1`. Rewrite using `[K'.card_res, hU.1, hd, pow_zero, one_pow]`. Establish `h2` using `Finite.one_lt_card (α := IsLocalRing.ResidueField K'.O)`. Use linear arithmetic over natural numbers and integers.
-/
theorem IsUnrExt.ne_zero {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) : d ≠ 0 := by
  intro hd
  have h1 : Nat.card (IsLocalRing.ResidueField K'.O) = 1 := by
    rw [K'.card_res, hU.1, hd, pow_zero, one_pow]
  have h2 := Finite.one_lt_card (α := IsLocalRing.ResidueField K'.O)
  omega

/- English proof (translation)
Use `letI : Algebra K.E K'.E := φ.toAlgebra`. Use `letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra`. Use `haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : FiniteDimensional K.E K'.E := Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact Nat.pos_of_ne_zero hU.ne_zero)`. Establish `h` using `Algebra.isIntegral_trace (R := K.O) (L := K.E) hz`.

Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h`. Conclude with `⟨a, ha.symm⟩`.
-/
theorem trace_int_of_isIntegral {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (z : K'.E)
    (hz : @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra z) :
    ∃ a : K.O, @Algebra.trace K.E K'.E _ _ φ.toAlgebra z = algebraMap K.O K.E a := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K.E K'.E :=
    Module.finite_of_finrank_pos (by rw [hU.2.2.2.2]; exact Nat.pos_of_ne_zero hU.ne_zero)
  have h := Algebra.isIntegral_trace (R := K.O) (L := K.E) hz
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  exact ⟨a, ha.symm⟩

end GlobalTheory.UnitLemma.Unr
