import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

/- English proof (translation)
Introduce `k r h hg`. Take `⟨hk, -, -, h4⟩` from `hg`. Establish `hAG : 0 ≤ AG k r` using `by unfold AG; positivity`. Establish `hA : 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 2 ≤ aOf r h - 1` using `by linarith`. Establish `hN : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2` using `by positivity`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Unfold `JF.TransportedAlt`. Rewrite using `[Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities. Establish `hAB : B.AB k r = AG k r / 2 + 1` using `by unfold B.AB AG; ring`.

Rewrite using `[hAB]`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thresholds_of_gapOK : ∀ (k r : ℕ) (h : ℝ), GapOK k r h →
    JF.TransportedAlt k r (aOf r h - 1) 0 ∧ B.AB k r ≤ aOf r h - 1 ∧ AG k r < (aOf r h - 1) / 2 ∧ 0 < aOf r h - 1 := by
  intro k r h hg
  obtain ⟨hk, -, -, h4⟩ := hg
  have hAG : 0 ≤ AG k r := by unfold AG; positivity
  have hA : 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + 3 * AG k r + 2 ≤ aOf r h - 1 := by linarith
  have hN : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold JF.TransportedAlt
    rw [Nat.cast_zero, mul_zero, sub_zero, lt_div_iff₀ (by positivity)]
    nlinarith
  · have hAB : B.AB k r = AG k r / 2 + 1 := by unfold B.AB AG; ring
    rw [hAB]
    linarith
  · linarith
  · linarith

end GlobalTheory
