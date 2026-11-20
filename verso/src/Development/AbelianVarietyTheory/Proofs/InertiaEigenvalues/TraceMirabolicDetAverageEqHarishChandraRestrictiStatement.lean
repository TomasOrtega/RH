import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMirabolicDetAverageEqHarishChandraRestricti
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FTraceMirabolicDetAverageEqHarishChandraRestricti.lean&line=181#L181)
-/
theorem _root_.GlobalTheory.T.trace_mirabolicDetAverage_eq_harishChandraRestriction : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ) (ψ : Gn g (n + 1) → ℂ) (θ : (ZMod g)ˣ →* ℂˣ),
    tr (mirEl θ (Pi.single (Fin.last n) 1) false) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res n 1 ψ 1 x ∧
      tr (mirEl θ (Pi.single 0 1) true) ψ =
        (g : ℂ) ^ n * ∑ x : Gn g 1, ((θ (Matrix.GeneralLinearGroup.det x) : ℂˣ) : ℂ) * res 1 n ψ x 1 := by
  first | exact @GlobalTheory.ResTr.trace_mir | exact GlobalTheory.ResTr.trace_mir | (intros; apply GlobalTheory.ResTr.trace_mir <;> assumption)
