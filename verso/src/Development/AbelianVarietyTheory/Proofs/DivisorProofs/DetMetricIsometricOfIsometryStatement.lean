import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricIsometricOfIsometry
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CurveDens.det_isometric_of_isIsometry` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDetMetricIsometricOfIsometry.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.det_metric_isometric_of_isometry : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (E E' : X.Modules) (r : ℕ) (h : VMetric p E r) (h' : VMetric p E' r) (H : h.IsCInf) (H' : h'.IsCInf) (φ : E ≅ E'), h.IsIsometry h' φ → (VMetric.det H).Isometric (VMetric.det H') := by
  first | exact @GlobalTheory.CurveDens.det_isometric_of_isIsometry | exact GlobalTheory.CurveDens.det_isometric_of_isIsometry | (intros; apply GlobalTheory.CurveDens.det_isometric_of_isIsometry <;> assumption)
