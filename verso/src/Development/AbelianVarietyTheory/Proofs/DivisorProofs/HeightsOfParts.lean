import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundLogRatioHalfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerBoundLogRatioUnitStatement
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4
open scoped ComplexOrder

namespace GlobalTheory.Mean4

/- English proof (translation)
Introduce `D Y A inner hF hA H c₀ hc₀`. Take `⟨t₀, ht₀, C, hC, H⟩` from `H c₀ hc₀`. Take `⟨C₁, h₁⟩` from `GlobalTheory.T.lower_bound_log_ratio_half C`. Take `⟨C₂, h₂⟩` from `GlobalTheory.T.lower_bound_log_ratio_unit C hC`. Use `⟨min t₀ (1 / 2), lt_min ht₀ (by norm_num), max (max C₁ C₂) (3 * C), ?_⟩` and prove the remaining obligations.

Introduce `B hB u t hu hs ht htt hg hcp _`. Establish `htR : (0 : ℝ) < (t : ℝ)` using `by exact_mod_cast ht`. Establish `hth : (t : ℝ) ≤ 1 / 2` using `htt.trans (min_le_right _ _)`. Take `⟨Hi, Hb, Hd⟩` from `H B hB u t hu hs ht (htt.trans (min_le_left _ _)) hg hcp`. Establish `hs0 : (0 : ℝ) < (t : ℝ) ^ 2` using `by positivity`.

Establish `hs1 : (t : ℝ) ^ 2 ≤ 1` using `by nlinarith`. Establish `hlog : 0 ≤ Real.log (B / (t : ℝ) ^ 2)`. Apply `Real.log_nonneg` to reduce the goal to its premises. Rewrite using `[le_div_iff₀ hs0]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlB : (1 : ℝ) / 2 ≤ Real.log B`. Use `Real.log_two_gt_d9` as an intermediate fact. Establish `h2` using `Real.log_le_log (by norm_num : (0 : ℝ) < 2) hB`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨fun y => ?_, fun c => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `hy : inner y`. Use `h₁ B t _ _ hB htR hth (le_max_right (hF y) 0) (Hi y hy)` as an intermediate fact. Establish `hle : C₁ ≤ max (max C₁ C₂) (3 * C)` using `(le_max_left _ _).trans (le_max_left _ _)`. Use `mul_le_mul_of_nonneg_right hle hlog` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `h₂ B _ _ _ hB hs0 hs1 (Hb y hy).1 (Hb y hy).2` as an intermediate fact. Establish `hle : C₂ ≤ max (max C₁ C₂) (3 * C)` using `(le_max_right _ _).trans (le_max_left _ _)`. Use `mul_le_mul_of_nonneg_right hle hlog` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨Z, hZ, hZ'⟩` from `Hd c`.

Use `⟨Z, hZ, fun y hy => (hZ' y hy).trans ?_⟩` and prove the remaining obligations. Establish `hle : 3 * C ≤ max (max C₁ C₂) (3 * C)` using `le_max_right _ _`. Use `mul_le_mul_of_nonneg_right hle (by linarith : 0 ≤ Real.log B)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem heights_of_parts : ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (A : SlopeTestRemainingChoices Y), ∀ (inner : Y.Pt → Prop) (hF hA : Y.Pt → ℝ), (∀ c₀ : ℝ, 0 < c₀ → ∃ t₀ : ℝ, 0 < t₀ ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt Y) (t : ℚ), IsRat Y u → supAbs Y u ≤ 1 → 0 < t → (t : ℝ) ≤ t₀ → (∀ τ, (t : ℝ) ≤ gap Y u τ) → CptGaps Y c₀ u → (∀ y, inner y → (t : ℝ) / 4 * max (hF y) 0 - C * Real.log (2 + max (hF y) 0) - C * Real.log B - C ≤ A.ht (Y.Mbar B u (t ^ 2)) y) ∧ (∀ y, ¬ inner y → -C ≤ hA y ∧ (t : ℝ) ^ 2 * hA y - C * Real.log (2 + C + hA y) - C * Real.log (B / (t : ℝ) ^ 2) - C ≤ A.ht (Y.Mbar B u (t ^ 2)) y) ∧ ∀ c, ∃ Z, A.dense c Z ∧ ∀ y ∈ Z, A.ht (Y.Mbar B u (t ^ 2)) y ≤ C * Real.log B + C) → Heights A := by
  intro D Y A inner hF hA H c₀ hc₀
  obtain ⟨t₀, ht₀, C, hC, H⟩ := H c₀ hc₀
  obtain ⟨C₁, h₁⟩ := GlobalTheory.T.lower_bound_log_ratio_half C
  obtain ⟨C₂, h₂⟩ := GlobalTheory.T.lower_bound_log_ratio_unit C hC
  refine ⟨min t₀ (1 / 2), lt_min ht₀ (by norm_num), max (max C₁ C₂) (3 * C), ?_⟩
  intro B hB u t hu hs ht htt hg hcp _
  have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
  have hth : (t : ℝ) ≤ 1 / 2 := htt.trans (min_le_right _ _)
  obtain ⟨Hi, Hb, Hd⟩ := H B hB u t hu hs ht (htt.trans (min_le_left _ _)) hg hcp
  have hs0 : (0 : ℝ) < (t : ℝ) ^ 2 := by positivity
  have hs1 : (t : ℝ) ^ 2 ≤ 1 := by nlinarith
  have hlog : 0 ≤ Real.log (B / (t : ℝ) ^ 2) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hs0]
    linarith
  have hlB : (1 : ℝ) / 2 ≤ Real.log B := by
    have := Real.log_two_gt_d9
    have h2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hB
    linarith
  refine ⟨fun y => ?_, fun c => ?_⟩
  · by_cases hy : inner y
    · have := h₁ B t _ _ hB htR hth (le_max_right (hF y) 0) (Hi y hy)
      have hle : C₁ ≤ max (max C₁ C₂) (3 * C) := (le_max_left _ _).trans (le_max_left _ _)
      have := mul_le_mul_of_nonneg_right hle hlog
      linarith
    · have := h₂ B _ _ _ hB hs0 hs1 (Hb y hy).1 (Hb y hy).2
      have hle : C₂ ≤ max (max C₁ C₂) (3 * C) := (le_max_right _ _).trans (le_max_left _ _)
      have := mul_le_mul_of_nonneg_right hle hlog
      linarith
  · obtain ⟨Z, hZ, hZ'⟩ := Hd c
    refine ⟨Z, hZ, fun y hy => (hZ' y hy).trans ?_⟩
    have hle : 3 * C ≤ max (max C₁ C₂) (3 * C) := le_max_right _ _
    have := mul_le_mul_of_nonneg_right hle (by linarith : 0 ≤ Real.log B)
    nlinarith

end GlobalTheory.Mean4
