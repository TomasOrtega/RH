import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLargePrimeDvdIntPolynomialEvalStatement
open scoped TensorProduct Polynomial

namespace GlobalTheory

open Polynomial

/- English proof (translation)
Take `⟨a, b, hab⟩` from `hf`. Take `⟨c1, hc1⟩` from `IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) a`. Take `⟨c2, hc2⟩` from `IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) b`. Use `set A := IsLocalization.integerNormalization (nonZeroDivisors ℤ) a`. Use `set B := IsLocalization.integerNormalization (nonZeroDivisors ℤ) b`.

Use `⟨(c2 : ℤ) • A, (c1 : ℤ) • B, (c1 : ℤ) * c2, ?_, ?_⟩` and prove the remaining obligations. Conclude with `mul_ne_zero (nonZeroDivisors.coe_ne_zero c1) (nonZeroDivisors.coe_ne_zero c2)`. Apply `Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)` to reduce the goal to its premises. Establish `e1 : A.map (Int.castRingHom ℚ) = ((c1 : ℤ) : ℚ) • a`. Rewrite using `[show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hc1]`.

Conclude with `(Int.cast_smul_eq_zsmul ℚ _ _).symm`. Establish `e2 : B.map (Int.castRingHom ℚ) = ((c2 : ℤ) : ℚ) • b`. Rewrite using `[show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hc2]`. Conclude with `(Int.cast_smul_eq_zsmul ℚ _ _).symm`. Simplify using `only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_smul, Polynomial.map_C, ← Polynomial.derivative_map, e1, e2]`.

Rewrite using `[smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[C_mul]`. Simplify using `only [eq_intCast]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = _ := by rw [hab, mul_one]; simp`.
-/
theorem int_bezout_derivative_of_separable (f : ℤ[X])
    (hf : (f.map (Int.castRingHom ℚ)).Separable) :
    ∃ A B : ℤ[X], ∃ N : ℤ, N ≠ 0 ∧ A * f + B * derivative f = C N := by
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨c1, hc1⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) a
  obtain ⟨c2, hc2⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors ℤ) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors ℤ) b
  refine ⟨(c2 : ℤ) • A, (c1 : ℤ) • B, (c1 : ℤ) * c2, ?_, ?_⟩
  · exact mul_ne_zero (nonZeroDivisors.coe_ne_zero c1) (nonZeroDivisors.coe_ne_zero c2)
  · apply Polynomial.map_injective (Int.castRingHom ℚ) (RingHom.injective_int _)
    have e1 : A.map (Int.castRingHom ℚ) = ((c1 : ℤ) : ℚ) • a := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hc1]
      exact (Int.cast_smul_eq_zsmul ℚ _ _).symm
    have e2 : B.map (Int.castRingHom ℚ) = ((c2 : ℤ) : ℚ) • b := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, hc2]
      exact (Int.cast_smul_eq_zsmul ℚ _ _).symm
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_smul, Polynomial.map_C,
      ← Polynomial.derivative_map, e1, e2]
    rw [smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul, smul_eq_C_mul]
    calc _ = C (((c1 : ℤ) : ℚ) * ((c2 : ℤ) : ℚ)) *
            (a * map (Int.castRingHom ℚ) f + b * derivative (map (Int.castRingHom ℚ) f)) := by
          rw [C_mul]; simp only [eq_intCast]; ring
      _ = _ := by rw [hab, mul_one]; simp

/- English proof (translation)
Introduce `f hdeg hsep n`. Take `⟨A, B, N, hN, hAB⟩` from `int_bezout_derivative_of_separable f hsep`. Take `⟨p, hp, hnp, x, hx⟩` from `GlobalTheory.T.exists_large_prime_dvd_int_polynomial_eval f hdeg (max n N.natAbs)`. Use `⟨p, hp, lt_of_le_of_lt (le_max_left _ _) hnp, ?_⟩` and prove the remaining obligations. Establish `hpZ : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`.

Establish `hev : A.eval x * f.eval x + B.eval x * (derivative f).eval x = N`. Use `congrArg (Polynomial.eval x) hAB` as an intermediate fact. Simplify using `using this`. Establish `hpN : ¬ (p : ℤ) ∣ N`. Introduce `h`.

Establish `h1` using `Int.natAbs_dvd_natAbs.mpr h`. Simplify using `only [Int.natAbs_natCast] at h1`. Establish `h2` using `Nat.le_of_dvd (Int.natAbs_pos.mpr hN) h1`. Establish `h3` using `lt_of_le_of_lt (le_max_right n N.natAbs) hnp`. Use linear arithmetic over natural numbers and integers.

Establish `hpd : ¬ (p : ℤ) ∣ (derivative f).eval x`. Introduce `h`. Apply `hpN` to reduce the goal to its premises. Rewrite using `[← hev]`. Conclude with `dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right h _)`.

Establish `hcop : IsCoprime ((derivative f).eval x) (p : ℤ)`. Rewrite using `[isCoprime_comm]`. Conclude with `(Prime.coprime_iff_not_dvd hpZ).mpr hpd`. Take `⟨u, v, huv⟩` from `hcop`. Take `⟨k, hk⟩` from `hx`.

Take `⟨K, hK⟩` from `Polynomial.binomExpansion f x ((p : ℤ) * (-(k * u)))`. Use `⟨x + (p : ℤ) * (-(k * u)), ?_⟩` and prove the remaining obligations. Rewrite using `[hK, hk]`. Use `⟨k * v + K * (k * u) ^ 2, ?_⟩` and prove the remaining obligations. Establish `: k = k * (u * (derivative f).eval x + v * p)` using `by rw [huv, mul_one]`.

Take the linear combination `(p : ℤ) * this`.
-/
theorem sep_int_poly_root_mod_prime_sq :
    ∀ f : ℤ[X], 0 < f.natDegree → (f.map (Int.castRingHom ℚ)).Separable →
      ∀ n : ℕ, ∃ p : ℕ, p.Prime ∧ n < p ∧ ∃ x : ℤ, ((p : ℤ) ^ 2) ∣ f.eval x := by
  intro f hdeg hsep n
  obtain ⟨A, B, N, hN, hAB⟩ := int_bezout_derivative_of_separable f hsep
  obtain ⟨p, hp, hnp, x, hx⟩ := GlobalTheory.T.exists_large_prime_dvd_int_polynomial_eval f hdeg (max n N.natAbs)
  refine ⟨p, hp, lt_of_le_of_lt (le_max_left _ _) hnp, ?_⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hev : A.eval x * f.eval x + B.eval x * (derivative f).eval x = N := by
    have := congrArg (Polynomial.eval x) hAB
    simpa using this
  have hpN : ¬ (p : ℤ) ∣ N := by
    intro h
    have h1 := Int.natAbs_dvd_natAbs.mpr h
    simp only [Int.natAbs_natCast] at h1
    have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hN) h1
    have h3 := lt_of_le_of_lt (le_max_right n N.natAbs) hnp
    omega
  have hpd : ¬ (p : ℤ) ∣ (derivative f).eval x := by
    intro h
    apply hpN
    rw [← hev]
    exact dvd_add (dvd_mul_of_dvd_right hx _) (dvd_mul_of_dvd_right h _)
  have hcop : IsCoprime ((derivative f).eval x) (p : ℤ) := by
    rw [isCoprime_comm]
    exact (Prime.coprime_iff_not_dvd hpZ).mpr hpd
  obtain ⟨u, v, huv⟩ := hcop
  obtain ⟨k, hk⟩ := hx
  obtain ⟨K, hK⟩ := Polynomial.binomExpansion f x ((p : ℤ) * (-(k * u)))
  refine ⟨x + (p : ℤ) * (-(k * u)), ?_⟩
  rw [hK, hk]
  refine ⟨k * v + K * (k * u) ^ 2, ?_⟩
  have : k = k * (u * (derivative f).eval x + v * p) := by rw [huv, mul_one]
  linear_combination (p : ℤ) * this

end GlobalTheory
