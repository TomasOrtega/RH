import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory

/- English proof (translation)
Introduce `Cc C₀ hC₀`. Establish `habs : 0 ≤ |Cc|` using `abs_nonneg _`. Establish `hle : Cc ≤ |Cc|` using `le_abs_self _`. Use `⟨|Cc| + C₀ + 40, by linarith, ?_⟩` and prove the remaining obligations. Introduce `Cg hCg k r n₀ p₀ h d hk hn hp hh hd`.

Establish `hk' : (1 : ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hn' : (n₀ : ℝ) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6` using `by exact_mod_cast hn`. Establish `hr : (0 : ℝ) ≤ r` using `Nat.cast_nonneg r`. Unfold `ThreeDimData.aOf`. Move the coercions through the operations in `at hh ⊢`.

Take `⟨R, hR⟩ : ∃ R : ℝ, R = (r : ℝ) + 1` from `⟨_, rfl⟩`. Establish `hrR : (r : ℝ) = R - 1` using `by linarith`. Establish `e1 : 2 * (r : ℝ) + 2 = 2 * R` using `by linarith`. Establish `e2 : (r : ℝ) + 2 = R + 1` using `by linarith`. Rewrite `hh`, the goal using `[e1]`.

Rewrite using `[e2]`. Rewrite `hh`, `hn'`, `hp`, the goal using `[← hR]`. Establish `hR1 : 1 ≤ R` using `by linarith`. Take `⟨N, hN⟩ : ∃ N : ℝ, N = 2 * (r : ℝ) + k + 1` from `⟨_, rfl⟩`. Rewrite `hh`, the goal using `[← hN]`.

Establish `hN2 : 2 ≤ N` using `by linarith`. Take `⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 3 * R * N ^ 2 + N ^ 3` from `⟨_, rfl⟩`. Rewrite `hh`, the goal using `[← hQ]`. Establish `hQ1 : 2 ≤ Q`. Establish `h1 : 0 ≤ 3 * R * N ^ 2` using `by positivity`.

Establish `h2 : (2 : ℝ) ^ 3 ≤ N ^ 3` using `pow_le_pow_left₀ (by norm_num) hN2 3`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR0 : 0 < R` using `by linarith`. Establish `hR2 : 1 ≤ R ^ 2` using `one_le_pow₀ hR1`. Establish `hR3 : 1 ≤ R ^ 3` using `one_le_pow₀ hR1`.

Establish `hR23 : R ^ 2 ≤ R ^ 3` using `pow_le_pow_right₀ hR1 (by norm_num)`. Establish `hR13 : R ≤ R ^ 3`. Use `pow_le_pow_right₀ hR1 (show 1 ≤ 3 by norm_num)` as an intermediate fact. Simplify using `using this`. Establish `hR34 : R ^ 3 ≤ R ^ 4` using `pow_le_pow_right₀ hR1 (by norm_num)`.

Establish `hA : R * p₀ ≤ C₀ * R ^ 3`. Use `mul_le_mul_of_nonneg_left hp hR0.le` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hB : R * n₀ ≤ 36 * R ^ 3`. Use `mul_le_mul_of_nonneg_left hn' hR0.le` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Establish `hC3 : 0 ≤ C₀ * R ^ 3` using `by positivity`. Establish `hCg0 : 0 ≤ Cg` using `by linarith`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hs : 0 < Real.sqrt (2 * R)` using `Real.sqrt_pos.mpr (by linarith)`.

Establish `hpow : (2 * R) ^ ((9 : ℝ) / 2) = (2 * R) ^ 4 * Real.sqrt (2 * R)`. Rewrite using `[Real.sqrt_eq_rpow, show (9 : ℝ) / 2 = ((4 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add (by linarith), Real.rpow_natCast]`. Rewrite `hh` using `[hpow]`. Establish `h1 : Cg * (R ^ 4 * Q) ≤ h / 2 / (8 * Real.sqrt (2 * R))`. Rewrite using `[le_div_iff₀ (by positivity)]`.

Establish `: Cg * (R ^ 4 * Q) * (8 * Real.sqrt (2 * R)) = Cg * ((2 * R) ^ 4 * Real.sqrt (2 * R) * Q) / 2` using `by ring`. Rewrite using `[this]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX : 2 * R ^ 3 ≤ R ^ 4 * Q`. Establish `: R ^ 4 * 2 ≤ R ^ 4 * Q` using `mul_le_mul_of_nonneg_left hQ1 (by positivity)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hX0 : 0 ≤ R ^ 4 * Q` using `by linarith`. Establish `h2 : (|Cc| + C₀ + 40) * (R ^ 4 * Q) ≤ Cg * (R ^ 4 * Q)` using `mul_le_mul_of_nonneg_right hCg hX0`. Establish `h3 : Cc * (R ^ 4 * Q) ≤ |Cc| * (R ^ 4 * Q)` using `mul_le_mul_of_nonneg_right hle hX0`. Establish `h4 : C₀ * (2 * R ^ 3) ≤ C₀ * (R ^ 4 * Q)` using `mul_le_mul_of_nonneg_left hX hC₀`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h1` using `le_max_left (Cg * (2 * R) ^ 3) (200 * d)`. Establish `h2` using `le_max_right (Cg * (2 * R) ^ 3) (200 * d)`. Establish `h3 : (C₀ + 40) * R ^ 3 ≤ Cg * R ^ 3` using `mul_le_mul_of_nonneg_right (by linarith) (by positivity)`. Establish `h4 : Cg * (2 * R) ^ 3 = 8 * (Cg * R ^ 3)` using `by ring`.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem margin_arith_closing : ∀ Cc C₀ : ℝ, 0 ≤ C₀ → ∃ Cg₀ : ℝ, 0 ≤ Cg₀ ∧ ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ (k r n₀ p₀ : ℕ) (h d : ℝ), 1 ≤ k → n₀ ≤ 30 * (r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * ((r : ℝ) + 1) ^ 2 → Cg * (((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) * (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)) ≤ h → 0 ≤ d → (Cc * ((r : ℝ) + 1) ^ 4 * (((3 * (r + 1) : ℕ) : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ (ThreeDimData.aOf r (h / 2) - 1) - (((2 * r + 2) * p₀ + n₀ * (r + 1) : ℕ) : ℝ)) ∧ d + (((2 * r + 2) * p₀ + n₀ * (r + 1) : ℕ) : ℝ) ≤ max (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ 3) (200 * d) / 2 - 1 ∧ (((r + 1) * (2 * p₀ + n₀) + (r + 1) * (r + 2) : ℕ) : ℝ) ≤ (C₀ + 10) * ((2 * r + 2 : ℕ) : ℝ) ^ 3 := by
  intro Cc C₀ hC₀
  have habs : 0 ≤ |Cc| := abs_nonneg _
  have hle : Cc ≤ |Cc| := le_abs_self _
  refine ⟨|Cc| + C₀ + 40, by linarith, ?_⟩
  intro Cg hCg k r n₀ p₀ h d hk hn hp hh hd
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn' : (n₀ : ℝ) ≤ 30 * ((r : ℝ) + 1) ^ 2 + 6 := by exact_mod_cast hn
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  unfold ThreeDimData.aOf
  push_cast at hh ⊢
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = (r : ℝ) + 1 := ⟨_, rfl⟩
  have hrR : (r : ℝ) = R - 1 := by linarith
  have e1 : 2 * (r : ℝ) + 2 = 2 * R := by linarith
  have e2 : (r : ℝ) + 2 = R + 1 := by linarith
  rw [e1] at hh ⊢
  rw [e2]
  rw [← hR] at hh hn' hp ⊢
  have hR1 : 1 ≤ R := by linarith
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = 2 * (r : ℝ) + k + 1 := ⟨_, rfl⟩
  rw [← hN] at hh ⊢
  have hN2 : 2 ≤ N := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 3 * R * N ^ 2 + N ^ 3 := ⟨_, rfl⟩
  rw [← hQ] at hh ⊢
  have hQ1 : 2 ≤ Q := by
    have h1 : 0 ≤ 3 * R * N ^ 2 := by positivity
    have h2 : (2 : ℝ) ^ 3 ≤ N ^ 3 := pow_le_pow_left₀ (by norm_num) hN2 3
    linarith
  have hR0 : 0 < R := by linarith
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR1
  have hR3 : 1 ≤ R ^ 3 := one_le_pow₀ hR1
  have hR23 : R ^ 2 ≤ R ^ 3 := pow_le_pow_right₀ hR1 (by norm_num)
  have hR13 : R ≤ R ^ 3 := by
    have := pow_le_pow_right₀ hR1 (show 1 ≤ 3 by norm_num)
    simpa using this
  have hR34 : R ^ 3 ≤ R ^ 4 := pow_le_pow_right₀ hR1 (by norm_num)
  have hA : R * p₀ ≤ C₀ * R ^ 3 := by
    have := mul_le_mul_of_nonneg_left hp hR0.le
    calc R * p₀ ≤ R * (C₀ * R ^ 2) := this
      _ = C₀ * R ^ 3 := by ring
  have hB : R * n₀ ≤ 36 * R ^ 3 := by
    have := mul_le_mul_of_nonneg_left hn' hR0.le
    calc R * n₀ ≤ R * (30 * R ^ 2 + 6) := this
      _ = 30 * R ^ 3 + 6 * R := by ring
      _ ≤ _ := by linarith
  have hC3 : 0 ≤ C₀ * R ^ 3 := by positivity
  have hCg0 : 0 ≤ Cg := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have hs : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr (by linarith)
    have hpow : (2 * R) ^ ((9 : ℝ) / 2) = (2 * R) ^ 4 * Real.sqrt (2 * R) := by
      rw [Real.sqrt_eq_rpow, show (9 : ℝ) / 2 = ((4 : ℕ) : ℝ) + 1 / 2 by norm_num,
        Real.rpow_add (by linarith), Real.rpow_natCast]
    rw [hpow] at hh
    have h1 : Cg * (R ^ 4 * Q) ≤ h / 2 / (8 * Real.sqrt (2 * R)) := by
      rw [le_div_iff₀ (by positivity)]
      have : Cg * (R ^ 4 * Q) * (8 * Real.sqrt (2 * R))
          = Cg * ((2 * R) ^ 4 * Real.sqrt (2 * R) * Q) / 2 := by ring
      rw [this]
      linarith
    have hX : 2 * R ^ 3 ≤ R ^ 4 * Q := by
      have : R ^ 4 * 2 ≤ R ^ 4 * Q := mul_le_mul_of_nonneg_left hQ1 (by positivity)
      linarith
    have hX0 : 0 ≤ R ^ 4 * Q := by linarith
    have h2 : (|Cc| + C₀ + 40) * (R ^ 4 * Q) ≤ Cg * (R ^ 4 * Q) :=
      mul_le_mul_of_nonneg_right hCg hX0
    have h3 : Cc * (R ^ 4 * Q) ≤ |Cc| * (R ^ 4 * Q) := mul_le_mul_of_nonneg_right hle hX0
    have h4 : C₀ * (2 * R ^ 3) ≤ C₀ * (R ^ 4 * Q) := mul_le_mul_of_nonneg_left hX hC₀
    nlinarith
  · have h1 := le_max_left (Cg * (2 * R) ^ 3) (200 * d)
    have h2 := le_max_right (Cg * (2 * R) ^ 3) (200 * d)
    have h3 : (C₀ + 40) * R ^ 3 ≤ Cg * R ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 : Cg * (2 * R) ^ 3 = 8 * (Cg * R ^ 3) := by ring
    nlinarith
  · nlinarith

end GlobalTheory
