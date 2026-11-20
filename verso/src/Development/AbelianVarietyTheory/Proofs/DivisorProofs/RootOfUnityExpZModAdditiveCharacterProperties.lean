import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.AddCharZMod

/- English proof (translation)
Rewrite using `[ZMod.stdAddChar_apply, ZMod.toCircle_apply]`. Both sides reduce to the same expression.
-/
theorem ch_eq (N : ℕ) [NeZero N] (j : ZMod N) : ch N j = ZMod.stdAddChar j := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

/- English proof (translation)
Introduce `N _`. Establish `hpow : ∀ (m : ℕ) (j : ZMod N), ch N ((m : ZMod N) * j) = ch N j ^ m`. Introduce `m j`. Rewrite using `[ch_eq, ch_eq, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]`. Establish `hadd : ∀ i j, ch N (i + j) = ch N i * ch N j`.

Introduce `i j`. Rewrite using `[ch_eq, ch_eq, ch_eq]`. Conclude with `AddChar.map_add_eq_mul _ i j`. Establish `hzero : ch N 0 = 1`. Rewrite using `[ch_eq]`.

Conclude with `AddChar.map_zero_eq_one _`. Use `⟨fun n => ?_, hadd, hzero, fun j => ?_, hpow, fun j => ?_, fun j => ?_, fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[ch_eq]`. Conclude with `ZMod.stdAddChar_coe n`. Rewrite using `[ch_eq, ← (ZMod.stdAddChar (N := N)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff]`.

Establish `h : ch N (-j) * ch N j = 1`. Rewrite using `[← hadd, neg_add_cancel, hzero]`. Conclude with `eq_inv_of_mul_eq_one_left h`. Rewrite using `[ch_eq, ZMod.stdAddChar_apply]`. Conclude with `Circle.norm_coe _`.

Establish `h : ch N j ^ N = 1`. Rewrite using `[← hpow, ZMod.natCast_self, zero_mul, hzero]`. Use `IsIntegral.of_pow (Nat.pos_of_neZero N) ?_` and prove the remaining obligations. Rewrite using `[h]`. Conclude with `isIntegral_one`.
-/
theorem main : ∀ (N : ℕ) [NeZero N], (∀ n : ℤ, ch N (n : ZMod N) = Complex.exp (2 * Real.pi * Complex.I * n / N)) ∧ (∀ i j, ch N (i + j) = ch N i * ch N j) ∧ ch N 0 = 1 ∧ (∀ j, ch N j = 1 ↔ j = 0) ∧ (∀ (m : ℕ) j, ch N ((m : ZMod N) * j) = ch N j ^ m) ∧ (∀ j, ch N (-j) = (ch N j)⁻¹) ∧ (∀ j, ‖ch N j‖ = 1) ∧ (∀ j, IsIntegral ℤ (ch N j)) := by
  intro N _
  have hpow : ∀ (m : ℕ) (j : ZMod N), ch N ((m : ZMod N) * j) = ch N j ^ m := by
    intro m j
    rw [ch_eq, ch_eq, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hadd : ∀ i j, ch N (i + j) = ch N i * ch N j := by
    intro i j
    rw [ch_eq, ch_eq, ch_eq]
    exact AddChar.map_add_eq_mul _ i j
  have hzero : ch N 0 = 1 := by
    rw [ch_eq]
    exact AddChar.map_zero_eq_one _
  refine ⟨fun n => ?_, hadd, hzero, fun j => ?_, hpow, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [ch_eq]
    exact ZMod.stdAddChar_coe n
  · rw [ch_eq, ← (ZMod.stdAddChar (N := N)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff]
  · have h : ch N (-j) * ch N j = 1 := by
      rw [← hadd, neg_add_cancel, hzero]
    exact eq_inv_of_mul_eq_one_left h
  · rw [ch_eq, ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  · have h : ch N j ^ N = 1 := by
      rw [← hpow, ZMod.natCast_self, zero_mul, hzero]
    refine IsIntegral.of_pow (Nat.pos_of_neZero N) ?_
    rw [h]
    exact isIntegral_one

end GlobalTheory.WpFam.AddCharZMod
