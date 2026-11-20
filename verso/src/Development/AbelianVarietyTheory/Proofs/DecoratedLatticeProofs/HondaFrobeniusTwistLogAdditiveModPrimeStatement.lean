import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFrobeniusTwistLogAdditiveModPrime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Honda.twistLog_additive_mod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FHondaFrobeniusTwistLogAdditiveModPrime.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.hondaFrobeniusTwistLog_additive_mod_prime : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ (i : ℕ), 0 < i → ∀ m, ‖MvPowerSeries.coeff m (Formalism.L2.Th1.C.be0 f e (frobOp σ l i f) (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)))‖ ≤ ‖(l : K)‖ := by
  first | exact @GlobalTheory.Honda.twistLog_additive_mod | exact GlobalTheory.Honda.twistLog_additive_mod | (intros; apply GlobalTheory.Honda.twistLog_additive_mod <;> assumption)
