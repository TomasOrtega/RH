import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace

namespace UpperTheory.Gal.FiniteEtaleModels

/- English proof (translation)
Introduce `A _ _ Q P htop hpow hmul 𝔞`. Proceed by induction on `𝔞 using UniqueFactorizationMonoid.induction_on_coprime with`. Consider the case `h0 => exact fun h => absurd rfl h`. Consider the case `h1 hx`. Name the introduced variables `x`.

Introduce `_ _`. Rewrite using `[Ideal.isUnit_iff.1 hx]`. Conclude with `htop`. Consider the case `hpr i hp`. Name the introduced variables `w`.

Introduce `_ hQ`. Break down `Nat.eq_zero_or_pos i with rfl | hi` into its components or cases. Rewrite using `[pow_zero, Ideal.one_eq_top]`. Conclude with `htop`. Establish `hmax : w.IsMaximal` using `(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero`.

Conclude with `hpow w i hmax (hQ w hmax (Ideal.pow_le_self hi.ne'))`. Consider the case `hcp hxy hx hy`. Name the introduced variables `x y`. Introduce `hne hQ`. Establish `hx0 : x ≠ ⊥` using `fun h => hne (by rw [h]; exact Ideal.bot_mul y)`.

Establish `hy0 : y ≠ ⊥` using `fun h => hne (by rw [h]; exact Ideal.mul_bot x)`. Establish `hsup : x ⊔ y = ⊤` using `Ideal.isUnit_iff.1 (hxy (Ideal.dvd_iff_le.2 le_sup_left) (Ideal.dvd_iff_le.2 le_sup_right))`. Conclude with `hmul x y hsup (hx hx0 fun w hw hle => hQ w hw (Ideal.mul_le_left.trans hle)) (hy hy0 fun w hw hle => hQ w hw (Ideal.mul_le_right.trans hle))`.
-/
theorem idealInd_holds : IdealInd := by
  intro A _ _ Q P htop hpow hmul 𝔞
  induction 𝔞 using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact fun h => absurd rfl h
  | h1 hx =>
    rename_i x
    intro _ _
    rw [Ideal.isUnit_iff.1 hx]
    exact htop
  | hpr i hp =>
    rename_i w
    intro _ hQ
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, Ideal.one_eq_top]
      exact htop
    · have hmax : w.IsMaximal :=
        (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
      exact hpow w i hmax (hQ w hmax (Ideal.pow_le_self hi.ne'))
  | hcp hxy hx hy =>
    rename_i x y
    intro hne hQ
    have hx0 : x ≠ ⊥ := fun h => hne (by rw [h]; exact Ideal.bot_mul y)
    have hy0 : y ≠ ⊥ := fun h => hne (by rw [h]; exact Ideal.mul_bot x)
    have hsup : x ⊔ y = ⊤ :=
      Ideal.isUnit_iff.1 (hxy (Ideal.dvd_iff_le.2 le_sup_left) (Ideal.dvd_iff_le.2 le_sup_right))
    exact hmul x y hsup
      (hx hx0 fun w hw hle => hQ w hw (Ideal.mul_le_left.trans hle))
      (hy hy0 fun w hw hle => hQ w hw (Ideal.mul_le_right.trans hle))

end UpperTheory.Gal.FiniteEtaleModels
