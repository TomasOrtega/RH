import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernCurvatureModelGramConjugateEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FChernCurvatureModelGramConjugateEmbedding.lean&line=111#L111)
-/
theorem _root_.GlobalTheory.T.chernCurvature_modelGram_conjugateEmbedding : ∀ {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n), (1 - (Z w)ᴴ * Z w).PosDef → curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η = -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := by
  first | exact @GlobalTheory.PointChern.curv_modelGram_tauBar | exact GlobalTheory.PointChern.curv_modelGram_tauBar | (intros; apply GlobalTheory.PointChern.curv_modelGram_tauBar <;> assumption)
