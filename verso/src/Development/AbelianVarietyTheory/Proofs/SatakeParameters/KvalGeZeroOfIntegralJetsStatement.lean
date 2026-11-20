import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KvalGeZeroOfIntegralJets
import Formalism.SharpRestriction.Divisibility.ProductZerothFirstParts
import Formalism.GaussJetBounds.StatementN
open Formalism.MainNotions Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FKvalGeZeroOfIntegralJets.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.kvalGe_zero_of_integral_jets : ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N0 N1 l : ℕ) [Fact l.Prime] (nu : Lt → YoungDiagram) (Th : MvPowerSeries (Lt × Fin N0 × Fin N1) ℂ_[l]), Formalism.DworkPowerSeriesWeights.JetsIntegral Th → product_zeroth_first_parts.KvalGe N0 N1 l nu Th 0 := by
  first | exact @GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero | exact GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero | (intros; apply GlobalTheory.Proof.kvalGe_zero_of_integral_jets.kvalGe_zero <;> assumption)
