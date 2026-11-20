import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundsUniformLargeGapFamilies
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GapAmpUniform.amplitude_bounds_uniform_gap` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAmplitudeBoundsUniformLargeGapFamilies.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.amplitude_bounds_uniform_large_gap_families : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 A C1 : ℝ, ∃ C C2 Ch thr : ℝ, 0 ≤ C ∧ 0 ≤ Ch ∧ ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cpr : ℝ, ∀ δ > 0, (OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlus.AmplitudeBoundsConjunction (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ) := by
  first | exact @GlobalTheory.GapAmpUniform.amplitude_bounds_uniform_gap | exact GlobalTheory.GapAmpUniform.amplitude_bounds_uniform_gap | (intros; apply GlobalTheory.GapAmpUniform.amplitude_bounds_uniform_gap <;> assumption)
