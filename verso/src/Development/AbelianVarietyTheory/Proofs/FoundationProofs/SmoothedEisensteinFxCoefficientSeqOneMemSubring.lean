import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Integral

open Finset

namespace GlobalTheory.KummerEisensteinGalois

open Finset in

/- English proof (translation)
Introduce `K _ _ R c M ζ a b hM hcop ha hb hbneg n`. Establish `hca : ¬ (M : ℤ) ∣ (c : ℤ) * a`. Introduce `h`. Apply `ha` to reduce the goal to its premises. Use `Int.dvd_of_dvd_mul_right_of_gcd_one h ?_` and prove the remaining obligations.

Rewrite using `[Int.gcd_natCast_natCast]`. Conclude with `Nat.Coprime.symm hcop`. Establish `hpow : ∀ m : ℕ, ζ ^ (b * (m : ℤ)) ∈ R ∧ ζ ^ (-(b * (m : ℤ))) ∈ R`. Introduce `m`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[zpow_mul, zpow_natCast]`. Conclude with `R.pow_mem hb m`. Rewrite using `[← neg_mul, zpow_mul, zpow_natCast]`. Conclude with `R.pow_mem hbneg m`. Establish `hpow' : ∀ m : ℕ, ζ ^ ((c : ℤ) * b * (m : ℤ)) ∈ R ∧ ζ ^ (-((c : ℤ) * b * (m : ℤ))) ∈ R`.

Introduce `m`. Establish `h` using `hpow (c * m)`. Rewrite using `[show (c : ℤ) * b * (m : ℤ) = b * ((c * m : ℕ) : ℤ) by push_cast; ring]` and apply the resulting hypothesis. Unfold `_root_.GlobalTheory.KummerEisensteinGalois.smF _root_.GlobalTheory.KummerEisensteinGalois.eisF`. Use `split_ifs with hn`.

Unfold `_root_.GlobalTheory.KummerEisensteinGalois.const0`. Simplify using `only [if_true, if_neg ha, if_neg hca]`. Establish `hM0 : (M : ℚ) ≠ 0` using `by exact_mod_cast hM.ne'`. Establish `key : (c : ℚ) ^ 2 * (1 / 2 - _root_.GlobalTheory.KummerEisensteinGalois.frc M a) - c * (1 / 2 - _root_.GlobalTheory.KummerEisensteinGalois.frc M (c * a)) = (((c.choose 2 : ℕ) : ℤ) - ((c : ℤ) * ((c : ℤ) * a / M) - (c : ℤ) ^ 2 * (a / M)) : ℤ)`. Unfold `_root_.GlobalTheory.KummerEisensteinGalois.frc`.

Rewrite using `[Int.emod_def, Int.emod_def]`. Use `push_cast`. Rewrite using `[Nat.cast_choose_two]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `intCast_mem R (((c.choose 2 : ℕ) : ℤ) - ((c : ℤ) * ((c : ℤ) * a / M) - (c : ℤ) ^ 2 * (a / M))) using 1` and compare the differences between its conclusion and the goal. Establish `hK` using `congrArg (fun q : ℚ => (q : K)) key`. Simplify using `only [Rat.cast_intCast] at hK`. Rewrite using `[← hK]`. Use `push_cast`.

Evaluate the numerical expressions. Unfold `_root_.GlobalTheory.KummerEisensteinGalois.coefPos`. Use `R.sub_mem (R.mul_mem (R.pow_mem (intCast_mem R _) 2) (R.sum_mem fun d _ => ?_)) (R.mul_mem ?_ (R.sum_mem fun d _ => ?_))` and prove the remaining obligations. Simplify using `only [Nat.sub_self, pow_zero, one_mul]`. Apply the tactic sequence `refine R.sub_mem ?_ ?_ <;> split_ifs`.

Conclude with `(hpow d).1`. Conclude with `R.zero_mem`. Conclude with `(hpow d).2`. Conclude with `R.zero_mem`. Evaluate the numerical expressions.

Simplify using `only [Nat.sub_self, pow_zero, one_mul]`. Apply the tactic sequence `refine R.sub_mem ?_ ?_ <;> split_ifs`. Conclude with `(hpow' d).1`. Conclude with `R.zero_mem`. Conclude with `(hpow' d).2`.

Conclude with `R.zero_mem`.
-/
theorem _root_.GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring : ∀ (K : Type) [Field K] [CharZero K]
    (R : Subring K) (c M : ℕ) (ζ : K) (a b : ℤ),
    0 < M → Nat.Coprime c M → ¬ (M : ℤ) ∣ a → ζ ^ b ∈ R → ζ ^ (-b) ∈ R →
    ∀ n : ℕ, _root_.GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M ζ a b n ∈ R := by
  intro K _ _ R c M ζ a b hM hcop ha hb hbneg n
  have hca : ¬ (M : ℤ) ∣ (c : ℤ) * a := by
    intro h
    apply ha
    refine Int.dvd_of_dvd_mul_right_of_gcd_one h ?_
    rw [Int.gcd_natCast_natCast]
    exact Nat.Coprime.symm hcop
  have hpow : ∀ m : ℕ, ζ ^ (b * (m : ℤ)) ∈ R ∧ ζ ^ (-(b * (m : ℤ))) ∈ R := by
    intro m
    refine ⟨?_, ?_⟩
    · rw [zpow_mul, zpow_natCast]; exact R.pow_mem hb m
    · rw [← neg_mul, zpow_mul, zpow_natCast]; exact R.pow_mem hbneg m
  have hpow' : ∀ m : ℕ, ζ ^ ((c : ℤ) * b * (m : ℤ)) ∈ R ∧ ζ ^ (-((c : ℤ) * b * (m : ℤ))) ∈ R := by
    intro m
    have h := hpow (c * m)
    rwa [show (c : ℤ) * b * (m : ℤ) = b * ((c * m : ℕ) : ℤ) by push_cast; ring]
  unfold _root_.GlobalTheory.KummerEisensteinGalois.smF _root_.GlobalTheory.KummerEisensteinGalois.eisF
  split_ifs with hn
  · unfold _root_.GlobalTheory.KummerEisensteinGalois.const0
    simp only [if_true, if_neg ha, if_neg hca]
    have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have key : (c : ℚ) ^ 2 * (1 / 2 - _root_.GlobalTheory.KummerEisensteinGalois.frc M a) -
        c * (1 / 2 - _root_.GlobalTheory.KummerEisensteinGalois.frc M (c * a)) =
        (((c.choose 2 : ℕ) : ℤ) - ((c : ℤ) * ((c : ℤ) * a / M) - (c : ℤ) ^ 2 * (a / M)) : ℤ) := by
      unfold _root_.GlobalTheory.KummerEisensteinGalois.frc
      rw [Int.emod_def, Int.emod_def]
      push_cast
      rw [Nat.cast_choose_two]
      field_simp
      ring
    convert intCast_mem R (((c.choose 2 : ℕ) : ℤ) - ((c : ℤ) * ((c : ℤ) * a / M) -
      (c : ℤ) ^ 2 * (a / M))) using 1
    have hK := congrArg (fun q : ℚ => (q : K)) key
    simp only [Rat.cast_intCast] at hK
    rw [← hK]
    push_cast
    norm_num
  · unfold _root_.GlobalTheory.KummerEisensteinGalois.coefPos
    refine R.sub_mem (R.mul_mem (R.pow_mem (intCast_mem R _) 2) (R.sum_mem fun d _ => ?_))
      (R.mul_mem ?_ (R.sum_mem fun d _ => ?_))
    · simp only [Nat.sub_self, pow_zero, one_mul]
      refine R.sub_mem ?_ ?_ <;> split_ifs
      · exact (hpow d).1
      · exact R.zero_mem
      · exact (hpow d).2
      · exact R.zero_mem
    · norm_num
    · simp only [Nat.sub_self, pow_zero, one_mul]
      refine R.sub_mem ?_ ?_ <;> split_ifs
      · exact (hpow' d).1
      · exact R.zero_mem
      · exact (hpow' d).2
      · exact R.zero_mem

end GlobalTheory.KummerEisensteinGalois
