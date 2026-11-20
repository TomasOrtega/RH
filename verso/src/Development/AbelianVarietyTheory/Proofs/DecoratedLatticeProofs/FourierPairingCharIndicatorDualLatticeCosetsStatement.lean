import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingCharIndicatorDualLatticeCosets
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FFourierPairingCharIndicatorDualLatticeCosets.lean&line=161#L161)
-/
theorem _root_.GlobalTheory.T.fourierPairing_charIndicator_dualLattice_cosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle) (hχ : HasConductor χ 1) (e : k), (e = 1 ∨ e = -1) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (Q : Pair k n), fpair χ e μ (charInd (resChar χ hχ q) Q) (dualInd Q.lat + ∑ Q'' ∈ withLat Q.lat, cosetInd q Q''.lat Q''.red) = fpair χ e μ (vecInd Q.lat) (dualInd Q.lat) := by
  first | exact @GlobalTheory.FinPl.Comm.DualCosets.fpair_charInd_dualInd_add_cosets | exact GlobalTheory.FinPl.Comm.DualCosets.fpair_charInd_dualInd_add_cosets | (intros; apply GlobalTheory.FinPl.Comm.DualCosets.fpair_charInd_dualInd_add_cosets <;> assumption)
