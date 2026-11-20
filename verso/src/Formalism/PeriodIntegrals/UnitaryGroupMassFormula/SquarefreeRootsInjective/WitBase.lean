import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.ClaimOf

open Polynomial

noncomputable section

namespace PI.SqfRootsInj.W

open PI.SqfLab

/- English proof (translation)
Establish `hdvd : ℓ ^ (orderOf x).factorization ℓ ∣ orderOf x` using `Nat.ordProj_dvd _ ℓ`. Establish `hmpos : 0 < orderOf x / ℓ ^ (orderOf x).factorization ℓ` using `Nat.div_pos (Nat.le_of_dvd hx hdvd) (pow_pos hℓ.pos _)`. Establish `hcop : Nat.Coprime (ℓ ^ (orderOf x).factorization ℓ) (orderOf x / ℓ ^ (orderOf x).factorization ℓ)` using `(Nat.coprime_ordCompl hℓ hx.ne').pow_left _`. Use `haveI : NeZero (orderOf x / ℓ ^ (orderOf x).factorization ℓ) := ⟨hmpos.ne'⟩`. Establish `hu : ((ℓ ^ (orderOf x).factorization ℓ * (((ℓ ^ (orderOf x).factorization ℓ : ℕ) : ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ))⁻¹).val : ℕ) : ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ)) = ((1 : ℕ) : ZMod _)`.

Rewrite using `[Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]`. Conclude with `ZMod.coe_mul_inv_eq_one _ hcop`. Rewrite `hu` using `[ZMod.natCast_eq_natCast_iff]`. Establish `hmod` using `Nat.ModEq.mul_left' (ℓ ^ (orderOf x).factorization ℓ) hu`. Rewrite `hmod` using `[Nat.mul_div_cancel' hdvd, mul_one]`.

Unfold `primeToPart`. Rewrite using `[← pow_mul, ← pow_mod_orderOf, mul_comm _ (ℓ ^ (orderOf x).factorization ℓ), ← hmod, pow_mod_orderOf]`.
-/
theorem pow_eq_part_pow {M : Type*} [Monoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x : M)
    (hx : 0 < orderOf x) :
    x ^ (ℓ ^ (orderOf x).factorization ℓ) =
      (primeToPart ℓ x) ^ (ℓ ^ (orderOf x).factorization ℓ) := by
  have hdvd : ℓ ^ (orderOf x).factorization ℓ ∣ orderOf x := Nat.ordProj_dvd _ ℓ
  have hmpos : 0 < orderOf x / ℓ ^ (orderOf x).factorization ℓ :=
    Nat.div_pos (Nat.le_of_dvd hx hdvd) (pow_pos hℓ.pos _)
  have hcop : Nat.Coprime (ℓ ^ (orderOf x).factorization ℓ)
      (orderOf x / ℓ ^ (orderOf x).factorization ℓ) :=
    (Nat.coprime_ordCompl hℓ hx.ne').pow_left _
  haveI : NeZero (orderOf x / ℓ ^ (orderOf x).factorization ℓ) := ⟨hmpos.ne'⟩
  have hu : ((ℓ ^ (orderOf x).factorization ℓ *
      (((ℓ ^ (orderOf x).factorization ℓ : ℕ) :
        ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ))⁻¹).val : ℕ) :
        ZMod (orderOf x / ℓ ^ (orderOf x).factorization ℓ)) = ((1 : ℕ) : ZMod _) := by
    rw [Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ hcop
  rw [ZMod.natCast_eq_natCast_iff] at hu
  have hmod := Nat.ModEq.mul_left' (ℓ ^ (orderOf x).factorization ℓ) hu
  rw [Nat.mul_div_cancel' hdvd, mul_one] at hmod
  unfold primeToPart
  rw [← pow_mul, ← pow_mod_orderOf, mul_comm _ (ℓ ^ (orderOf x).factorization ℓ), ← hmod,
    pow_mod_orderOf]

/- English proof (translation)
Establish `hx : 0 < orderOf x` using `Nat.pos_of_ne_zero fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hxN))`. Establish `hle : (orderOf x).factorization ℓ ≤ padicValNat ℓ N`. Rewrite using `[← Nat.factorization_def N hℓ]`. Conclude with `(Nat.factorization_le_iff_dvd hx.ne' hN).2 hxN ℓ`. Establish `key` using `pow_eq_part_pow ℓ hℓ x hx`.

Rewrite using `[← Nat.add_sub_cancel' hle, pow_add, pow_mul, pow_mul, key]`.
-/
theorem pow_eq_part_pow_of_dvd {M : Type*} [Monoid M] (ℓ : ℕ) (hℓ : ℓ.Prime) (x : M) (N : ℕ)
    (hN : N ≠ 0) (hxN : orderOf x ∣ N) :
    x ^ (ℓ ^ padicValNat ℓ N) = (primeToPart ℓ x) ^ (ℓ ^ padicValNat ℓ N) := by
  have hx : 0 < orderOf x := Nat.pos_of_ne_zero fun h => hN (Nat.eq_zero_of_zero_dvd (h ▸ hxN))
  have hle : (orderOf x).factorization ℓ ≤ padicValNat ℓ N := by
    rw [← Nat.factorization_def N hℓ]
    exact (Nat.factorization_le_iff_dvd hx.ne' hN).2 hxN ℓ
  have key := pow_eq_part_pow ℓ hℓ x hx
  rw [← Nat.add_sub_cancel' hle, pow_add, pow_mul, pow_mul, key]

/- English proof (translation)
Establish `hw : IsIntegral (ZMod g) w` using `Algebra.IsIntegral.isIntegral w`. Use `haveI : FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) {w}) := IntermediateField.adjoin.finiteDimensional hw`. Use `haveI : Finite (IntermediateField.adjoin (ZMod g) {w}) := Module.finite_of_finite (ZMod g)`. Use `letI : Fintype (IntermediateField.adjoin (ZMod g) {w}) := Fintype.ofFinite _`. Establish `hcard : Fintype.card (IntermediateField.adjoin (ZMod g) {w}) = g ^ (minpoly (ZMod g) w).natDegree`.

Rewrite using `[Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hw]`. Establish `h` using `FiniteField.pow_card (IntermediateField.AdjoinSimple.gen (ZMod g) w)`. Rewrite `h` using `[hcard]`. Establish `h2` using `congrArg Subtype.val h`. Simplify using `using h2`.
-/
theorem pow_card_minpoly {g : ℕ} [Fact g.Prime] (w : Fbar g) :
    w ^ (g ^ (minpoly (ZMod g) w).natDegree) = w := by
  have hw : IsIntegral (ZMod g) w := Algebra.IsIntegral.isIntegral w
  haveI : FiniteDimensional (ZMod g) (IntermediateField.adjoin (ZMod g) {w}) :=
    IntermediateField.adjoin.finiteDimensional hw
  haveI : Finite (IntermediateField.adjoin (ZMod g) {w}) :=
    Module.finite_of_finite (ZMod g)
  letI : Fintype (IntermediateField.adjoin (ZMod g) {w}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod g) {w}) =
      g ^ (minpoly (ZMod g) w).natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hw]
  have h := FiniteField.pow_card (IntermediateField.AdjoinSimple.gen (ZMod g) w)
  rw [hcard] at h
  have h2 := congrArg Subtype.val h
  simpa using h2

end PI.SqfRootsInj.W
