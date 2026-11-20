import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesCoeffNormLeOneRootCoprimePadic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RootInt.intSer_root` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPowerSeriesCoeffNormLeOneRootCoprimePadic.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.powerSeriesCoeffNormLeOne_root_coprime_padic : ∀ (p : ℕ) [Fact p.Prime] (N : ℕ), 0 < N → Nat.Coprime N p →
    ∀ s : PowerSeries ℂ_[p], PowerSeries.constantCoeff s = 1 →
      GlobalTheory.EvenTheta.IntSer (s ^ N) → GlobalTheory.EvenTheta.IntSer s := by
  first | exact @GlobalTheory.RootInt.intSer_root | exact GlobalTheory.RootInt.intSer_root | (intros; apply GlobalTheory.RootInt.intSer_root <;> assumption)
