import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalDoubleCosetRepsMul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ZonalSum.sum_mul_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FSumBorelSphericalDoubleCosetRepsMul.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.sum_borelSpherical_doubleCosetReps_mul : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : Fin N → ℂ) (ψ : GL (Fin N) k → ℂ), IsBorelSph k γ ψ → (∀ i, γ i ≠ 0) → ∀ (g₀ : GL (Fin N) k) (R : Finset (GL (Fin N) k)), IsRepsK g₀ R → ∀ m : GL (Fin N) k, ∑ g ∈ R, ψ (m * g) = ψ m * ∑ g ∈ R, ψ g := by
  first | exact @GlobalTheory.ZonalSum.sum_mul_eq | exact GlobalTheory.ZonalSum.sum_mul_eq | (intros; apply GlobalTheory.ZonalSum.sum_mul_eq <;> assumption)
