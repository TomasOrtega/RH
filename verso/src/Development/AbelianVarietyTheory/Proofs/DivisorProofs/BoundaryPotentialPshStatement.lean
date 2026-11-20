import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialPsh
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticLogResolution
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PoincareLevi.levi_nonneg` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBoundaryPotentialPsh.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.boundary_potential_psh : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X)
    (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ (x : X) (j : Fin A.n), ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (α.U x ∩ (boundary σ)ᶜ),
      ∀ w : Fin d → ℂ, 0 ≤ levi ((fun z => α.φ x z + pFun Λ σ c z / 2) ∘ (A.chart j).symm) y w := by
  first | exact @GlobalTheory.PoincareLevi.levi_nonneg | exact GlobalTheory.PoincareLevi.levi_nonneg | (intros; apply GlobalTheory.PoincareLevi.levi_nonneg <;> assumption)
