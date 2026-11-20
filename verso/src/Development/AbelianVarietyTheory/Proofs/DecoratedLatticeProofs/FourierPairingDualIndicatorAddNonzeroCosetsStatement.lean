import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierPairingDualIndicatorAddNonzeroCosets
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FFourierPairingDualIndicatorAddNonzeroCosets.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.fourierPairing_dualIndicator_add_nonzeroCosets : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (χ : AddChar k Circle), HasConductor χ 1 → ∀ (e : k), (e = 1 ∨ e = -1) → ∀ (μ : Measure (n → k)) [μ.IsAddHaarMeasure] (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k], fpair χ e μ (vecInd L) (dualInd L + ∑ Q ∈ withLat L, cosetInd q Q.lat Q.red) = fpair χ e μ (vecInd L) (dualInd L) := by
  first | exact @GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets | exact GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets | (intros; apply GlobalTheory.FinPl.Comm.fpair_vecInd_dualInd_add_cosets <;> assumption)
