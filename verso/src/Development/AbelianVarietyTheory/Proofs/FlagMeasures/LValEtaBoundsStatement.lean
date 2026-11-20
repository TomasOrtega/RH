import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBounds
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EtaValueBound.lValEta_bounds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FLValEtaBounds.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.lValEta_mem_Icc_two_pow_fDeg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ i : ℕ, 2 ≤ i → ((2 : ℝ) ^ (Formalism.HermitianLatticesTheory.fDeg K))⁻¹ ≤ Formalism.HermitianLatticesTheory.lValEta K i ∧ Formalism.HermitianLatticesTheory.lValEta K i ≤ 2 ^ (Formalism.HermitianLatticesTheory.fDeg K) := by
  first | exact @GlobalTheory.EtaValueBound.lValEta_bounds | exact GlobalTheory.EtaValueBound.lValEta_bounds | (intros; apply GlobalTheory.EtaValueBound.lValEta_bounds <;> assumption)
