import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingPairCharIndicatorDualLatticeIndica
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.Comm.fpair_charInd_dualInd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FFourierPairingPairCharIndicatorDualLatticeIndica.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.fourierPairing_pairCharIndicator_dualLatticeIndicator_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n), fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat) = 0 := by
  first | exact @GlobalTheory.FinPl.Comm.fpair_charInd_dualInd | exact GlobalTheory.FinPl.Comm.fpair_charInd_dualInd | (intros; apply GlobalTheory.FinPl.Comm.fpair_charInd_dualInd <;> assumption)
