import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.RecordEigenInputs
import GroundTheory.HeightsAndTheta.Heights.MultinomialWeights.ExampleLimitPolynomialHypothesis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.TheoremB

namespace PrimesLogSum

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨C, hC⟩`. Establish `hC0 : 0 ≤ C`. Establish `h` using `hC 2 le_rfl ∅ (by simp) (by simp)`. Simplify using `only [Finset.sum_empty, Nat.cast_ofNat] at h`.

Establish `hl : 0 < Real.log 2` using `Real.log_pos (by norm_num)`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨C, fun B0 hB0 P hP hcard => ?_⟩` and prove the remaining obligations. Establish `hfl : 2 ≤ ⌊B0⌋₊` using `Nat.le_floor (by exact_mod_cast hB0)`. Establish `hcard' : P.card ≤ ⌊B0⌋₊` using `Nat.le_floor hcard`.

Establish `h` using `hC ⌊B0⌋₊ hfl P hP hcard'`. Establish `hpos : (0 : ℝ) < ⌊B0⌋₊` using `by exact_mod_cast (lt_of_lt_of_le (by norm_num) hfl)`. Establish `hlog : Real.log ⌊B0⌋₊ ≤ Real.log B0` using `Real.log_le_log hpos (Nat.floor_le (by linarith))`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨C, hC⟩`.

Use `⟨C, fun B hB P hP hcard => ?_⟩` and prove the remaining obligations. Conclude with `hC B (by exact_mod_cast hB) P hP (by exact_mod_cast hcard)`.
-/
theorem equiv : NineStatements.PrimeLogSum.Statement ↔ PrimesLogSum.Statement := by
  constructor
  · rintro ⟨C, hC⟩
    have hC0 : 0 ≤ C := by
      have h := hC 2 le_rfl ∅ (by simp) (by simp)
      simp only [Finset.sum_empty, Nat.cast_ofNat] at h
      have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith
    refine ⟨C, fun B0 hB0 P hP hcard => ?_⟩
    have hfl : 2 ≤ ⌊B0⌋₊ := Nat.le_floor (by exact_mod_cast hB0)
    have hcard' : P.card ≤ ⌊B0⌋₊ := Nat.le_floor hcard
    have h := hC ⌊B0⌋₊ hfl P hP hcard'
    have hpos : (0 : ℝ) < ⌊B0⌋₊ := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hfl)
    have hlog : Real.log ⌊B0⌋₊ ≤ Real.log B0 := Real.log_le_log hpos (Nat.floor_le (by linarith))
    calc ∑ p ∈ P, Real.log p / ((p : ℝ) - 1) ≤ C * Real.log ⌊B0⌋₊ := h
      _ ≤ C * Real.log B0 := mul_le_mul_of_nonneg_left hlog hC0
  · rintro ⟨C, hC⟩
    refine ⟨C, fun B hB P hP hcard => ?_⟩
    exact hC B (by exact_mod_cast hB) P hP (by exact_mod_cast hcard)

end PrimesLogSum

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.TheoremB
