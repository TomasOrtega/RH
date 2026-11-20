import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualLatticeCosetIndicatorIsSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField
open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FDualLatticeCosetIndicatorIsSchwartzBruhat.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] (f : Module.Dual 𝓀[k] (Red L)), cosetInd q L f ∈ SB (n → k) := by
  first | exact @GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB | exact GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB | (intros; apply GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB <;> assumption)
