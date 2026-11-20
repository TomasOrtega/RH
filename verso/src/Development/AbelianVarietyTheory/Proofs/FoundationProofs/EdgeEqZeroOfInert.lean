import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CobOn
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFirstChernClassOfLineBundle
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertFixesRootOfUnitRatio
open GlobalTheory.KEdge GlobalTheory.NeedB Polynomial

namespace GlobalTheory.EdgeUnr
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem val_lt_one_iff (B : ValuationSubring Ω) (z : Ω) : B.valuation z < 1 ↔ z = 0 ∨ z⁻¹ ∉ B := by
  by_cases hz : z = 0
  · simp [hz]
  · simp only [hz, false_or, ← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le]
    have : 0 < B.valuation z := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).mpr hz
    constructor
    · intro h; exact one_lt_inv₀ this |>.mpr h
    · intro h; exact (one_lt_inv₀ this).mp h

end GlobalTheory.EdgeUnr

namespace GlobalTheory.EdgeUnr

end GlobalTheory.EdgeUnr
