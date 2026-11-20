import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodTorusFlatCoordsInverse
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPeriodTorusFlatCoordsInverse.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.period_torus_flat_coords_inverse : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ b ∈ B, (∀ x, flatOf (τ b) (per (τ b) x) = x) ∧ ∀ z, per (τ b) (flatOf (τ b) z) = z := by
  first | exact @GlobalTheory.flatcoord_inverse | exact GlobalTheory.flatcoord_inverse | (intros; apply GlobalTheory.flatcoord_inverse <;> assumption)
