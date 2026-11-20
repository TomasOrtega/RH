import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalFinPartInCompactBoundedDenominator
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BoundedDen.bounded_den` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRationalFinPartInCompactBoundedDenominator.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.rational_finPart_in_compact_bounded_denominator : ∀ (D : D7) (K : Set (AE D)), IsCompact K → ∃ L : ℕ, 0 < L ∧ ∀ k ∈ K, ∀ x : D.host.E, finPart D (incA D x) = finPart D k → IsIntegral ℤ ((L : D.host.E) * x) := by
  first | exact @GlobalTheory.BoundedDen.bounded_den | exact GlobalTheory.BoundedDen.bounded_den | (intros; apply GlobalTheory.BoundedDen.bounded_den <;> assumption)
