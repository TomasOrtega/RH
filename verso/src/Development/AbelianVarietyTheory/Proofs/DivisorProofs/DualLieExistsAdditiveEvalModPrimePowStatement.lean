import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLieExistsAdditiveEvalModPrimePow
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.dual_lie_exists_eval_mod_pow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDualLieExistsAdditiveEvalModPrimePow.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.dual_lie_exists_additive_eval_mod_prime_pow : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (l : G.dual.Lie) (n : ℕ), ∃ (b : G.A n) (z : G.A n ⊗[O] G.A n), cobOne O (G.A n) b = (p : O) ^ n • z ∧ ∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit O φ = w.1 n → (p : O) ^ n ∣ l w - φ b := by
  first | exact @GlobalTheory.PDivGroup.dual_lie_exists_eval_mod_pow | exact GlobalTheory.PDivGroup.dual_lie_exists_eval_mod_pow | (intros; apply GlobalTheory.PDivGroup.dual_lie_exists_eval_mod_pow <;> assumption)
