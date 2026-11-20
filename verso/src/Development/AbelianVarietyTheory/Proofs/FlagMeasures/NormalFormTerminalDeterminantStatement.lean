import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormTerminalDeterminant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DegCnt.SplitIdx.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FNormalFormTerminalDeterminant.lean&line=326#L326)
-/
theorem _root_.GlobalTheory.T.normal_form_terminal_determinant : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.bI Λ ≠ 0 ∧ bOne N.F' N.F Λ N.j = N.bI Λ ∧ delBar N.F N.F' Λ * (N.bI Λ : ℝ) ^ 2 = N.Del ∧ 1 ≤ delBar N.F N.F' Λ := by
  first | exact @GlobalTheory.DegCnt.SplitIdx.main | exact GlobalTheory.DegCnt.SplitIdx.main | (intros; apply GlobalTheory.DegCnt.SplitIdx.main <;> assumption)
