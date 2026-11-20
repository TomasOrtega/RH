import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumPrimeLogDivPredLeLogAdd

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory.PrimeLogSum

open scoped BigOperators Matrix in
open Polynomial in

/- English proof (translation)
Introduce `B hB`. Establish `h` using `_root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le ⌊B⌋₊`. Establish `hN : (1 : ℝ) ≤ (⌊B⌋₊ : ℝ)`. Establish `: 1 ≤ ⌊B⌋₊` using `Nat.le_floor (by exact_mod_cast hB)`. Conclude with `this` after adjusting the coercions.

Establish `hle : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B` using `Nat.floor_le (by linarith)`. Establish `hlog : Real.log (⌊B⌋₊ : ℝ) ≤ Real.log B` using `Real.log_le_log (by linarith) hle`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem _root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le_real : ∀ (B : ℝ), 1 ≤ B →
    ∑ p ∈ (Finset.range (⌊B⌋₊ + 1)).filter Nat.Prime, Real.log p / ((p : ℝ) - 1)
      ≤ Real.log B + 3 := by
  intro B hB
  have h := _root_.GlobalTheory.PrimeLogSum.sum_log_div_pred_le ⌊B⌋₊
  have hN : (1 : ℝ) ≤ (⌊B⌋₊ : ℝ) := by
    have : 1 ≤ ⌊B⌋₊ := Nat.le_floor (by exact_mod_cast hB)
    exact_mod_cast this
  have hle : ((⌊B⌋₊ : ℕ) : ℝ) ≤ B := Nat.floor_le (by linarith)
  have hlog : Real.log (⌊B⌋₊ : ℝ) ≤ Real.log B :=
    Real.log_le_log (by linarith) hle
  linarith

end GlobalTheory.PrimeLogSum
