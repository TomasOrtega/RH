import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFlagPairLatticeSumDiscriminantEqNormMinor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DegCnt.FlagDisc.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHermFlagPairLatticeSumDiscriminantEqNormMinor.lean&line=308#L308)
-/
theorem _root_.GlobalTheory.T.hermFlagPairLatticeSumDiscriminant_eq_norm_minor : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ l ≤ N.j, N.nD l ≠ 0 → normD N.F N.F' Λ l = N.nD l ∧ 1 ≤ N.nD l := by
  first | exact @GlobalTheory.DegCnt.FlagDisc.main | exact GlobalTheory.DegCnt.FlagDisc.main | (intros; apply GlobalTheory.DegCnt.FlagDisc.main <;> assumption)
