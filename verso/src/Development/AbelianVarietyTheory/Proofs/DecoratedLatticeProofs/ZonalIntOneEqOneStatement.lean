import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntOneEqOne
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZonalOne.zonalInt_one_eq_one` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FZonalIntOneEqOne.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.zonalInt_one_eq_one_of_isBorelSph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → zonalInt μK ψ 1 = 1 := by
  first | exact @GlobalTheory.ZonalOne.zonalInt_one_eq_one | exact GlobalTheory.ZonalOne.zonalInt_one_eq_one | (intros; apply GlobalTheory.ZonalOne.zonalInt_one_eq_one <;> assumption)
