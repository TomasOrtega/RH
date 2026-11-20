import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerSeminormPolynomialGrowth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairRApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzTranslationSeminormBound
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchrodingerSeminormPolynomialGrowth.lean&line=44#L44)
-/
theorem _root_.GlobalTheory.T.schrodinger_seminorm_polynomial_growth : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {P : V → V → ℝ} (hP : GlobalTheory.ArchUniq.IsPairing P) (f : 𝓢(V, ℂ)), ∀ k m : ℕ, ∃ (C : ℝ) (N : ℕ), ∀ w : V × V, SchwartzMap.seminorm ℂ k m (GlobalTheory.SchrPairing.schrSch hP w f) ≤ C * (1 + ‖w‖) ^ N := by
  first | exact @GlobalTheory.SchrPairingGrowth.seminorm_schrSch_le | exact GlobalTheory.SchrPairingGrowth.seminorm_schrSch_le | (intros; apply GlobalTheory.SchrPairingGrowth.seminorm_schrSch_le <;> assumption)
