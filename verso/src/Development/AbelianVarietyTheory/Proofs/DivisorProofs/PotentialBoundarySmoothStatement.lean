import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialBoundarySmooth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BoundarySmooth.boundary_isClosed_and_smoothOn` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPotentialBoundarySmooth.lean&line=59#L59)
-/
theorem _root_.GlobalTheory.T.potential_boundary_smooth : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (m : ℕ)
    (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    (∀ i, IsPotential A (Λ i) ∧ IsSection A (Λ i) (σ i) ∧ ∀ y, normSec (Λ i) (σ i) y ≤ 1) →
    IsClosed (boundary σ) ∧ A.SmoothOn (boundary σ)ᶜ (fun y => pFun Λ σ c y / 2) := by
  first | exact @GlobalTheory.BoundarySmooth.boundary_isClosed_and_smoothOn | exact GlobalTheory.BoundarySmooth.boundary_isClosed_and_smoothOn | (intros; apply GlobalTheory.BoundarySmooth.boundary_isClosed_and_smoothOn <;> assumption)
