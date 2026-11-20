import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjInvariantDivisorNorm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ShFam.exists_isDivNorm_family` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsConjInvariantDivisorNorm.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.exists_conj_invariant_divisor_norm : ∀ (k : Type) [Field k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (d : ℕ) [SmoothOfRelativeDimension d p] (C : Closeds Y), IsProjOver p → (∀ σ : k →+* ℂ, (starRingEnd ℂ).comp σ ≠ σ) → ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal C) → ∃ n : ∀ σ : k →+* ℂ, CxPts p σ → ℝ, (∀ σ, IsDivNorm (AnRead.all p σ d) C (n σ)) ∧ ∀ σ σ' (j : CxPts p σ' → CxPts p σ), IsConjMap j → ∀ z, n σ' z = n σ (j z) := by
  first | exact @GlobalTheory.ShFam.exists_isDivNorm_family | exact GlobalTheory.ShFam.exists_isDivNorm_family | (intros; apply GlobalTheory.ShFam.exists_isDivNorm_family <;> assumption)
