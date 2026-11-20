import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointRowsSumEqDivisorSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowSumsTwoThreeClosedFormRealNonIntegerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.G2AddWeierstrassPRowSumStatement

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.ExpansionB

/- English proof (translation)
Introduce `h`. Establish `hN : (N : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr (NeZero.ne N)`. Rewrite `h` using `[div_eq_iff hN]`. Establish `h' : (j.val : ℤ) = n * (N : ℤ)` using `by exact_mod_cast h`. Apply `hj` to reduce the goal to its premises.

Establish `h2` using `congrArg (Int.cast : ℤ → ZMod N) h'`. Simplify using `using h2`.
-/
theorem val_div_ne_int (N : ℕ) [NeZero N] (j : ZMod N) (hj : j ≠ 0) (n : ℤ) :
    ((j.val : ℂ)) / N ≠ n := by
  intro h
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  rw [div_eq_iff hN] at h
  have h' : (j.val : ℤ) = n * (N : ℤ) := by exact_mod_cast h
  apply hj
  have h2 := congrArg (Int.cast : ℤ → ZMod N) h'
  simpa using h2

/- English proof (translation)
Introduce `N _ x hx`. Rewrite using `[hasQ_iff]`. Introduce `τ`. Take `⟨T, hT, hS⟩` from `GlobalTheory.T.torsionPoint_rows_sum_eq_divisor_series N 1 τ x _ le_rfl (GlobalTheory.T.G2_add_weierstrassP_row_sum τ (tors N τ x))`. Establish `hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0`.

Simplify using `[Real.pi_ne_zero]`. Establish `hT' : HasSum (fun k : ℕ => cSum N 1 1 x k * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ k) T`. Simplify using `using hT`. Use `set c : ℂ := (if x 0 = 0 then ch N (x 1) / (1 - ch N (x 1)) ^ 2 else 0) with hcdef`. Establish `hval : wB N x τ = T + c`.

Rewrite using `[wB_eq, hS, div_eq_iff (pow_ne_zero 2 hc), hcdef]`. Distinguish the cases in `h0 : x 0 = 0`. Establish `h1 : x 1 ≠ 0`. Introduce `h1`. Apply `hx` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `h0`. Conclude with `h1`. Establish `him : (((x 1).val : ℂ) / N).im = 0`.

Establish `: (((x 1).val : ℂ) / N) = ((((x 1).val : ℝ) / N : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[this, Complex.ofReal_im]`. Establish `hr` using `(GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger _ him (val_div_ne_int N (x 1) h1)).1`. Establish `hch : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((x 1).val : ℂ) / N)) = ch N (x 1)`. Rewrite using `[ch, mul_div_assoc]`.

Rewrite `hr` using `[hch]`. Rewrite using `[if_pos h0, if_pos h0]`. Establish `e2 : (1 + 1 : ℕ) = 2` using `rfl`. Rewrite using `[e2, hr]`. Simplify using `only [Nat.factorial_one, Nat.cast_one]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h0, if_neg h0]`. Simplify using `only [Nat.factorial_one, Nat.cast_one]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hval]`.

Establish `hs : HasSum (fun k : ℕ => if k = 0 then c else 0) c` using `hasSum_ite_eq 0 c`. Use `hT'.add hs using 2 with k` and compare the differences between its conclusion and the goal. Distinguish the cases in `hk : k = 0`. Substitute `hk` using the available equality. Simplify using `[cB, cSum, hcdef]`.

Simplify using `[cB, hk]`.
-/
theorem main : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), x ≠ 0 → HasQ N (wB N x) (cB N x) := by
  classical
  intro N _ x hx
  rw [hasQ_iff]
  intro τ
  obtain ⟨T, hT, hS⟩ := GlobalTheory.T.torsionPoint_rows_sum_eq_divisor_series N 1 τ x _ le_rfl (GlobalTheory.T.G2_add_weierstrassP_row_sum τ (tors N τ x))
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero]
  have hT' : HasSum (fun k : ℕ => cSum N 1 1 x k *
      Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * τ / N) ^ k) T := by
    simpa using hT
  set c : ℂ := (if x 0 = 0 then ch N (x 1) / (1 - ch N (x 1)) ^ 2 else 0) with hcdef
  have hval : wB N x τ = T + c := by
    rw [wB_eq, hS, div_eq_iff (pow_ne_zero 2 hc), hcdef]
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        apply hx
        funext i
        fin_cases i
        · exact h0
        · exact h1
      have him : (((x 1).val : ℂ) / N).im = 0 := by
        have : (((x 1).val : ℂ) / N) = ((((x 1).val : ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
        rw [this, Complex.ofReal_im]
      have hr := (GlobalTheory.T.rowSums_two_three_closedForm_real_nonInteger _ him (val_div_ne_int N (x 1) h1)).1
      have hch : Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (((x 1).val : ℂ) / N)) = ch N (x 1) := by
        rw [ch, mul_div_assoc]
      rw [hch] at hr
      rw [if_pos h0, if_pos h0]
      have e2 : (1 + 1 : ℕ) = 2 := rfl
      rw [e2, hr]
      simp only [Nat.factorial_one, Nat.cast_one]
      ring
    · rw [if_neg h0, if_neg h0]
      simp only [Nat.factorial_one, Nat.cast_one]
      ring
  rw [hval]
  have hs : HasSum (fun k : ℕ => if k = 0 then c else 0) c := hasSum_ite_eq 0 c
  convert hT'.add hs using 2 with k
  by_cases hk : k = 0
  · subst hk
    simp [cB, cSum, hcdef]
  · simp [cB, hk]

end GlobalTheory.WpFam.ExpansionB
