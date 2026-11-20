import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairNormPadicValuationBound
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.NormVal.norm_mem_and_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FDefiniteThetaPairNormPadicValuationBound.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.definiteThetaPairNorm_padicValuation_bound : ∀ (D : D7), Inp D → ∀ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl → ∀ (δ t0 : ℂ) (Q : ℕ), Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → GoodLevel D Q → ∀ (P : Pair D ⊤ δ t0 Q) (N : ℕ) (B : ℝ), P.Small N B → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ((P.norm : ℝ) : ℂ) ∈ Qbar ∧ ‖lamC lam ((P.norm : ℝ) : ℂ)‖ ≤ (p : ℝ) ^ (3 * ((padicValNat p (8 ^ (4 * fF D * N) * (8 * fF D * N).factorial) : ℝ) + 4 * fF D * N * B * (dl p + (if p = D.host.d then 1 / 4 else 0) + (padicValNat p Q : ℝ)) + 4 * (N : ℝ) ^ 2 * (padicValNat p Q : ℝ))) := by
  first | exact @GlobalTheory.NormVal.norm_mem_and_le | exact GlobalTheory.NormVal.norm_mem_and_le | (intros; apply GlobalTheory.NormVal.norm_mem_and_le <;> assumption)
