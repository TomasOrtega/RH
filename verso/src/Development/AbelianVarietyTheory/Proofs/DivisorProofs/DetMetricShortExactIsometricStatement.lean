import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.VMetric.isometric_det_tens_det` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDetMetricShortExactIsometric.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.det_metric_shortExact_isometric : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (S : ShortComplex X.Modules) (r s : ℕ) (h : VMetric p S.X₂ (r + s)) (H : h.IsCInf) (hS : S.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (hf : IsSubbundle S.f), ((VMetric.det (H.restrict hf h₁)).tens (VMetric.det (H.quot hS h₁ h₃))).Isometric (VMetric.det H) := by
  first | exact @GlobalTheory.VMetric.isometric_det_tens_det | exact GlobalTheory.VMetric.isometric_det_tens_det | (intros; apply GlobalTheory.VMetric.isometric_det_tens_det <;> assumption)
