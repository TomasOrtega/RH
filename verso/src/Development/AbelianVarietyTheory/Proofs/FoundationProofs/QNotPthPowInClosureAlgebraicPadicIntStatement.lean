import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QNotPthPowInClosureAlgebraicPadicInt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IntegralLocallyConstCochainModPow
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FQNotPthPowInClosureAlgebraicPadicInt.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.q_not_pth_pow_in_closure_algebraic_padicInt : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
      b ^ p ≠ algebraMap (O0 p) Ω (qO p) := by
  first | exact @GlobalTheory.K5.NotPow.q_not_pow | exact GlobalTheory.K5.NotPow.q_not_pow | (intros; apply GlobalTheory.K5.NotPow.q_not_pow <;> assumption)
