import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFactorHolomorphicSolution
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaDefect.defect` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FThetaFactorHolomorphicSolution.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.theta_factor_holomorphic_solution : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {B U : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ j : Fl g → Pt E g → ℂ, IsFactor B τ (stdLat g) j → InducesPolarisation B τ (stdLat g) j → IsOpen U → Convex ℝ U → U.Nonempty → U ⊆ B → ∀ G : Fl g → Pt E g → ℂ, (∀ l ∈ stdLat g, DifferentiableOn ℂ (G l) (cov U g) ∧ ∀ P ∈ cov U g, j l P = Complex.exp (2 * π * Complex.I * (thetaExp (τ P.1) l P.2 + G l P))) → ∃ c : Fl g → Fl g → ℤ, (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, c l l' = c l' l) ∧ (∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ l'' ∈ stdLat g, c l l' + c (l + l') l'' = c l (l' + l'') + c l' l'') ∧ ∀ l ∈ stdLat g, ∀ l' ∈ stdLat g, ∀ P ∈ cov U g, G (l + l') P = G l (transl τ l' P) + G l' P + c l l' := by
  first | exact @GlobalTheory.ThetaDefect.defect | exact GlobalTheory.ThetaDefect.defect | (intros; apply GlobalTheory.ThetaDefect.defect <;> assumption)
