import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesCoeffBoundedTaylorEllipticOfPoles
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FCpSeriesCoeffBoundedTaylorEllipticOfPoles.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.cpSeriesCoeffBounded_taylor_elliptic_of_poles : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ℓ : ℂ_[q]⟦X⟧) (φ : ℂ → ℂ), M.Chart ℓ → Ell M.L φ → AnalyticAt ℂ φ 0 → (∀ p, meromorphicOrderAt φ p < 0 → ¬ M.Small p) → Bdd (hat M.ι ℓ φ) := by
  first | exact @GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell | exact GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell | (intros; apply GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell <;> assumption)
