import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFrobeniusTwistLogEigenModPrime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Honda.frobLog_eigen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FHondaFrobeniusTwistLogEigenModPrime.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.hondaFrobeniusTwistLog_eigen_mod_prime : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ w : K, CoefLe 1 (Formalism.L2.Th1.C.mulBy f e w) → ∀ (i : ℕ), 0 < i → CoefLe ‖(l : K)‖ ((frobOp σ l i f).subst (Formalism.L2.Th1.C.mulBy f e w) - C ((σ ^ i) w) * frobOp σ l i f) := by
  first | exact @GlobalTheory.Honda.frobLog_eigen | exact GlobalTheory.Honda.frobLog_eigen | (intros; apply GlobalTheory.Honda.frobLog_eigen <;> assumption)
