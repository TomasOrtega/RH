import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricSmoothOffBoundary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FHodgeMetricSmoothOffBoundary.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.hodge_metric_smooth_off_boundary : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ), (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} := by
  first | exact @GlobalTheory.ShFam.ToroidalCompactificationData.hodge_smoothOn | exact GlobalTheory.ShFam.ToroidalCompactificationData.hodge_smoothOn | (intros; apply GlobalTheory.ShFam.ToroidalCompactificationData.hodge_smoothOn <;> assumption)
