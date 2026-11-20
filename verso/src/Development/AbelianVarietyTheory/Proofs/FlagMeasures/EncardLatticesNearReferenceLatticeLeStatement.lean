import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardLatticesNearReferenceLatticeLe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DegCnt.NearCount.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FEncardLatticesNearReferenceLatticeLe.lean&line=165#L165)
-/
theorem _root_.GlobalTheory.T.encard_lattices_near_reference_lattice_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ 𝔪 : Ideal (𝓞 K), 𝔪 ≠ ⊥ → ((({P : Submodule (𝓞 K) V | 𝔪 • N.P0 ≤ P ∧ 𝔪 • P ≤ N.P0}).encard : ℕ∞) : ℝ≥0∞) ≤ (Ideal.absNorm 𝔪 : ℝ≥0∞) ^ (2 * (2 * r + 1) ^ 2) := by
  first | exact @GlobalTheory.DegCnt.NearCount.main | exact GlobalTheory.DegCnt.NearCount.main | (intros; apply GlobalTheory.DegCnt.NearCount.main <;> assumption)
