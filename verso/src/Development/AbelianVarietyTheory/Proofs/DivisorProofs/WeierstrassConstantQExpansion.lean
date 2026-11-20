import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

/- English proof (translation)
Establish `hπ : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Simplify using `only [gN, EisensteinSeries.E2, Pi.smul_apply, smul_eq_mul, riemannZeta_two, mul_pow, Complex.I_sq]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem weierstrass_constant_eq_E2 (τ : ℍ) : gN τ = (-1 / 12) * EisensteinSeries.E2 τ := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [gN, EisensteinSeries.E2, Pi.smul_apply, smul_eq_mul, riemannZeta_two, mul_pow, Complex.I_sq]
  field_simp
  ring

/- English proof (translation)
Introduce `N _ τ`. Establish `hN : N ≠ 0` using `NeZero.ne N`. Establish `hNc : (N : ℂ) ≠ 0` using `by exact_mod_cast hN`. Establish `hinj : Function.Injective (fun m : ℕ => N * m)` using `fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h`. Rewrite using `[← hinj.hasSum_iff]`.

Establish `h` using `(EisensteinSeries.hasSum_qExpansion_E2 (z := τ)).mul_left (-1 / 12 : ℂ)`. Rewrite using `[weierstrass_constant_eq_E2]`. Use `convert! h using 1`. Use function extensionality and compare the values at `m`. Establish `he : Complex.exp (2 * Real.pi * Complex.I * ((N * m : ℕ) : ℂ) * τ / N) = Complex.exp (2 * Real.pi * Complex.I * τ) ^ m`.

Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Simplify using `only [Function.comp, he, smul_eq_mul]`.

Distinguish the cases in `hm : m = 0`. Simplify using `[hm, cG]`. Establish `h1 : N * m ≠ 0` using `mul_ne_zero hN hm`. Simplify using `only [cG, if_neg h1, if_neg hm, if_pos (dvd_mul_right N m), Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hN)]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `k hk`. Establish `hd : ¬ N ∣ k` using `fun ⟨m, hm⟩ => hk ⟨m, hm.symm⟩`. Establish `h0 : k ≠ 0` using `fun h => hd (h ▸ dvd_zero N)`. Simplify using `[cG, hd, h0]`.
-/
theorem hasQ_gN : ∀ (N : ℕ) [NeZero N], HasQ N gN (cG N) := by
  intro N _ τ
  have hN : N ≠ 0 := NeZero.ne N
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have hinj : Function.Injective (fun m : ℕ => N * m) := fun a b h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hN) h
  rw [← hinj.hasSum_iff]
  · have h := (EisensteinSeries.hasSum_qExpansion_E2 (z := τ)).mul_left (-1 / 12 : ℂ)
    rw [weierstrass_constant_eq_E2]
    convert! h using 1
    funext m
    have he : Complex.exp (2 * Real.pi * Complex.I * ((N * m : ℕ) : ℂ) * τ / N) =
        Complex.exp (2 * Real.pi * Complex.I * τ) ^ m := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp
    simp only [Function.comp, he, smul_eq_mul]
    by_cases hm : m = 0
    · simp [hm, cG]
    · have h1 : N * m ≠ 0 := mul_ne_zero hN hm
      simp only [cG, if_neg h1, if_neg hm, if_pos (dvd_mul_right N m),
        Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero hN)]
      ring
  · intro k hk
    have hd : ¬ N ∣ k := fun ⟨m, hm⟩ => hk ⟨m, hm.symm⟩
    have h0 : k ≠ 0 := fun h => hd (h ▸ dvd_zero N)
    simp [cG, hd, h0]

end GlobalTheory.WpFam
