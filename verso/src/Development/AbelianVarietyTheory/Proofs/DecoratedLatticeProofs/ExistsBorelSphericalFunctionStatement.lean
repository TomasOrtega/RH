import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalFunction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FExistsBorelSphericalFunction.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.exists_borelSphericalFunction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ), (∀ i, γ i ≠ 0) → ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k γ ψ := by
  first | exact @GlobalTheory.BorelSphExist.exists_isBorelSph | exact GlobalTheory.BorelSphExist.exists_isBorelSph | (intros; apply GlobalTheory.BorelSphExist.exists_isBorelSph <;> assumption)
