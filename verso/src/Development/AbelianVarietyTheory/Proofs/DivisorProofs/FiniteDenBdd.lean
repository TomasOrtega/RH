import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPairValueLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSumsVanishOfTrivialFlags
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalCharacterIdealPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalIdealFrobeniusProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRationalBoundedDenominators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementsBoundedPadic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedCoordinatesPPowerDenominator

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinFix

/- English proof (translation)
Establish `hN' : (0 : ℚ) < N` using `by exact_mod_cast hN`. Use `((Set.finite_Icc (-⌈R * N⌉) ⌈R * N⌉).image (fun k : ℤ => (k : ℚ) / N)).subset ?_` and prove the remaining obligations. Introduce and unpack `q ⟨⟨k, hk⟩, hR⟩`. Use `⟨k, ?_, ?_⟩` and prove the remaining obligations. Establish `hkR : |(k : ℝ)| ≤ R * N`.

Establish `: (k : ℝ) = (q : ℝ) * N` using `by exact_mod_cast hk.symm`. Rewrite using `[this, abs_mul, Nat.abs_cast]`. Conclude with `mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg _)`. Establish `h1` using `abs_le.1 hkR`. Prove the components needed by the constructor for the conclusion.

Establish `: -(R * N) ≤ (k : ℝ)` using `h1.1`. Establish `h3 : (-⌈R * N⌉ : ℝ) ≤ k`. Use `Int.le_ceil (R * N)` as an intermediate fact. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `h3` after adjusting the coercions. Establish `h3 : (k : ℝ) ≤ ⌈R * N⌉` using `le_trans h1.2 (Int.le_ceil _)`. Conclude with `h3` after adjusting the coercions. Use `show (k : ℚ) / N = q`. Rewrite using `[← hk]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem finite_den_bdd (N : ℕ) (hN : 0 < N) (R : ℝ) :
    {q : ℚ | (∃ k : ℤ, q * N = k) ∧ |(q : ℝ)| ≤ R}.Finite := by
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  refine ((Set.finite_Icc (-⌈R * N⌉) ⌈R * N⌉).image (fun k : ℤ => (k : ℚ) / N)).subset ?_
  rintro q ⟨⟨k, hk⟩, hR⟩
  refine ⟨k, ?_, ?_⟩
  · have hkR : |(k : ℝ)| ≤ R * N := by
      have : (k : ℝ) = (q : ℝ) * N := by exact_mod_cast hk.symm
      rw [this, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg _)
    have h1 := abs_le.1 hkR
    constructor
    · have : -(R * N) ≤ (k : ℝ) := h1.1
      have h3 : (-⌈R * N⌉ : ℝ) ≤ k := by
        have := Int.le_ceil (R * N); push_cast; linarith
      exact_mod_cast h3
    · have h3 : (k : ℝ) ≤ ⌈R * N⌉ := le_trans h1.2 (Int.le_ceil _)
      exact_mod_cast h3
  · show (k : ℚ) / N = q
    rw [← hk]; field_simp

end GlobalTheory.FinFix
