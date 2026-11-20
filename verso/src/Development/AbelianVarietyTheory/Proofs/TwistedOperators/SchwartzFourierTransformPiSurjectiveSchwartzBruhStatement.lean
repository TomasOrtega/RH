import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzFourierTransformPiSurjectiveSchwartzBruh
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SplitWeil.FourierSurj.hat_surjective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FSchwartzFourierTransformPiSurjectiveSchwartzBruh.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.schwartzFourierTransformPi_surjective_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) (_ : IsSelfDual ψ ν), (∀ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 ∈ SB (n → k)) ∧ ∀ g : SB (n → k), ∃ Φ₀ : SB (n → k), hat ψ ν Φ₀.1 = g.1 := by
  first | exact @GlobalTheory.SplitWeil.FourierSurj.hat_surjective | exact GlobalTheory.SplitWeil.FourierSurj.hat_surjective | (intros; apply GlobalTheory.SplitWeil.FourierSurj.hat_surjective <;> assumption)
