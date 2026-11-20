import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : HasSubst (addLaw R d)` using `hasSubst_of_constantCoeff_zero fun i => by simp [addLaw]`. Establish `h2 : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R))` using `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`. Establish `h3 : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R))` using `hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _`. Unfold `cob1 inL inR`. Rewrite using `[subst_pow h1, subst_pow h2, subst_pow h3, subst_X h1, subst_X h2, subst_X h3]`.

Simplify using `only [addLaw]`. Establish `hr : Finset.range (N + 1) = insert 0 (insert N (Finset.Ioo 0 N))`. Use extensionality with `i`. Simplify using `only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[add_pow, hr, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]`. Simplify using `only [pow_zero, Nat.sub_zero, Nat.sub_self, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one, mul_one, one_mul]`. Establish `key : ∀ i ∈ Finset.Ioo 0 N, (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R) ^ i * X (Sum.inr m) ^ (N - i) * (N.choose i : MvPowerSeries (Fin d ⊕ Fin d) R) = monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i)) (N.choose i : R)`. Introduce `i _`. Rewrite using `[X_pow_eq, X_pow_eq, monomial_mul_monomial, one_mul, ← nsmul_eq_mul', ← map_nsmul, nsmul_one]`.

Rewrite using `[Finset.sum_congr rfl key]`. Normalize the expressions using the abelian group laws.
-/
theorem coboundaryOne_additiveFormalGroupLaw_X_pow (R : Type) [CommRing R] (d N : ℕ) (m : Fin d) (hN : 1 ≤ N) :
    cob1 (addLaw R d) (X m ^ N) = ∑ i ∈ Finset.Ioo 0 N,
      monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i))
        (N.choose i : R) := by
  have h1 : HasSubst (addLaw R d) := hasSubst_of_constantCoeff_zero fun i => by simp [addLaw]
  have h2 : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have h3 : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  unfold cob1 inL inR
  rw [subst_pow h1, subst_pow h2, subst_pow h3, subst_X h1, subst_X h2, subst_X h3]
  simp only [addLaw]
  have hr : Finset.range (N + 1) = insert 0 (insert N (Finset.Ioo 0 N)) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [add_pow, hr, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp)]
  simp only [pow_zero, Nat.sub_zero, Nat.sub_self, Nat.choose_zero_right, Nat.choose_self,
    Nat.cast_one, mul_one, one_mul]
  have key : ∀ i ∈ Finset.Ioo 0 N,
      (X (Sum.inl m) : MvPowerSeries (Fin d ⊕ Fin d) R) ^ i * X (Sum.inr m) ^ (N - i) *
        (N.choose i : MvPowerSeries (Fin d ⊕ Fin d) R) =
      monomial (Finsupp.single (Sum.inl m) i + Finsupp.single (Sum.inr m) (N - i))
        (N.choose i : R) := by
    intro i _
    rw [X_pow_eq, X_pow_eq, monomial_mul_monomial, one_mul, ← nsmul_eq_mul', ← map_nsmul,
      nsmul_one]
  rw [Finset.sum_congr rfl key]
  abel

end GlobalTheory
