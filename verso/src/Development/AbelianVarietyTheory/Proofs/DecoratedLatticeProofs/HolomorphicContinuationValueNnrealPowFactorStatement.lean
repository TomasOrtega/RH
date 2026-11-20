import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HolomorphicContinuationValueNnrealPowFactor
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FHolomorphicContinuationValueNnrealPowFactor.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.holomorphicContinuationValue_nnrealPow_factor : ∀ (h h' : ℂ → ℂ) (s₀ c : ℂ) (r : ℝ≥0) (σ : ℝ), 0 < r → HolValueAt h s₀ c → (∀ s : ℂ, σ < s.re → h' s = npow r (s₀ - s) * h s) → HolValueAt h' s₀ c := by
  first | exact @GlobalTheory.StdUnn.holValueAt_npow_sub_mul | exact GlobalTheory.StdUnn.holValueAt_npow_sub_mul | (intros; apply GlobalTheory.StdUnn.holValueAt_npow_sub_mul <;> assumption)
