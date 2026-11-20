import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffChernPolyEqSumRepresentations
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FTopDegreeFormCoeffChernPolyEqSumRepresentations.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.topDegreeFormCoeff_chernPoly_eq_sum_representations : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (n : ℕ) (R : MvPolynomial (ι × ℕ) ℝ), ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (a : J → ℝ), ∀ A : Mat m (MvPolynomial (Fin n × Fin n) ℂ), (∀ τ i j, (A τ i j).IsHomogeneous 1) → topCoeff (aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-A x.1)).coeff x.2) R) = ∑ j, (a j : ℂ) * topCoeff ((Matrix.charpolyRev (-(ρ j).lie A)).coeff n) := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.topCoeff_chern_eq_sum_rep | exact GlobalTheory.GoodMetric.ChernSpan.topCoeff_chern_eq_sum_rep | (intros; apply GlobalTheory.GoodMetric.ChernSpan.topCoeff_chern_eq_sum_rep <;> assumption)
