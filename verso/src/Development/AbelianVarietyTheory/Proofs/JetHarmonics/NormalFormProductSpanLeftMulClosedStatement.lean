import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormProductSpanLeftMulClosed
import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HatNF.SpanMul.span_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FNormalFormProductSpanLeftMulClosed.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.normalFormProductSpan_left_mul_closed : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ T : Set A, (∀ i j n, ∀ x ∈ nfSpan d T i j n, (∀ b ∈ bmon d, b * x ∈ nfSpan d T i j n) ∧ d.L.Di * x ∈ nfSpan d T (i + 1) j n ∧ TL.gI d.L * x ∈ nfSpan d T i (j + 1) n) ∧ ∀ a : ℕ, (∀ X ∈ hats d.L, X ∈ nfSpan d T 0 a 1) → ∀ i j n, ∀ X ∈ hats d.L, ∀ x ∈ nfSpan d T i j n, X * x ∈ nfSpan d T i (j + a) (n + 1) := by
  first | exact @GlobalTheory.HatNF.SpanMul.span_mul | exact GlobalTheory.HatNF.SpanMul.span_mul | (intros; apply GlobalTheory.HatNF.SpanMul.span_mul <;> assumption)
