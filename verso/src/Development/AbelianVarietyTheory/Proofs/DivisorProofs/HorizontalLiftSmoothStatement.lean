import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalLiftSmooth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHorizontalLiftSmooth.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.horizontal_lift_smooth : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ), IsPeriodMap B τ → ∀ v : E, ContDiffOn ℝ ∞ (fun Q : Pt E g => hor τ Q v) (cov B g) := by
  first | exact @GlobalTheory.HorSmooth.horSmooth | exact GlobalTheory.HorSmooth.horSmooth | (intros; apply GlobalTheory.HorSmooth.horSmooth <;> assumption)
