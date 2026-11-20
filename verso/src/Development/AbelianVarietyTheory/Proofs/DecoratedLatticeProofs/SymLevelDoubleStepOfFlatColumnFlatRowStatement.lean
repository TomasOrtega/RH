import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelDoubleStepOfFlatColumnFlatRow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSymLevelDoubleStepOfFlatColumnFlatRow.lean&line=251#L251)
-/
theorem _root_.GlobalTheory.T.symLevel_doubleStep_of_flatColumn_flatRow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.OneIndexAt t ν → GlobalTheory.LocFlat.PureCol S t ν → GlobalTheory.LocFlat.PureRow S t ν → GlobalTheory.LocFlat.DoubleStep S t ν := by
  first | exact @GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow | exact GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow | (intros; apply GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow <;> assumption)
