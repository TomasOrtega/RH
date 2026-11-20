import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchwartzBruhatHalfIffPullbackMatrix
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HalfCoordSB.isSBHalf_iff_pull` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIsSchwartzBruhatHalfIffPullbackMatrix.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.isSchwartzBruhatHalf_iff_pullback_matrix : ∀ (D : D7) (S T : HSp D) (v : FinPl D) (m n : ℕ) (a : AE D) (Λ : AddSubgroup (WO S T)) (κ : WO S T → Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsCoord a Λ κ → (∀ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), IsSBHalf a Λ (pull a κ Φ)) ∧ ∀ Ψ, IsSBHalf a Λ Ψ → ∃ Φ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin m) (Fin n) (Fv D.host.F v)), Ψ = pull a κ Φ := by
  first | exact @GlobalTheory.HalfCoordSB.isSBHalf_iff_pull | exact GlobalTheory.HalfCoordSB.isSBHalf_iff_pull | (intros; apply GlobalTheory.HalfCoordSB.isSBHalf_iff_pull <;> assumption)
