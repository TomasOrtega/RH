import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalLiftPullback
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorsionForm.HorChain.hor_comp` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHorizontalLiftPullback.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.horizontal_lift_pullback : ∀ {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E'] {g : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (φ : E' → E) (P : Pt E' g) (v : E'), DifferentiableAt ℂ φ P.1 → (∀ i j, DifferentiableAt ℂ (fun b => τ b i j) (φ P.1)) → hor (τ ∘ φ) P v = (v, (hor τ (φ P.1, P.2) (fderiv ℂ φ P.1 v)).2) := by
  first | exact @GlobalTheory.TorsionForm.HorChain.hor_comp | exact GlobalTheory.TorsionForm.HorChain.hor_comp | (intros; apply GlobalTheory.TorsionForm.HorChain.hor_comp <;> assumption)
