import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairScalarEqQuotIdealsNormLe
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DegCnt.c_eq_quot_ideals` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHermFramePairScalarEqQuotIdealsNormLe.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.hermFramePair_scalar_eq_quot_ideals_norm_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ 𝔞 𝔞' : Ideal (𝓞 K), 𝔞 ≠ ⊥ ∧ 𝔞' ≠ ⊥ ∧ (Ideal.absNorm 𝔞 : ℝ) ≤ N.Del ∧ (Ideal.absNorm 𝔞' : ℝ) ≤ N.Del ∧ ∀ t : K, t * N.c ∈ ipow 𝔞 1 ↔ t ∈ ipow 𝔞' 1 := by
  first | exact @GlobalTheory.DegCnt.c_eq_quot_ideals | exact GlobalTheory.DegCnt.c_eq_quot_ideals | (intros; apply GlobalTheory.DegCnt.c_eq_quot_ideals <;> assumption)
