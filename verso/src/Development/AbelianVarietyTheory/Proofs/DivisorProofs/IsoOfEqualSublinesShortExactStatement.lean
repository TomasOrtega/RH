import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoOfEqualSublinesShortExact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsoOfEqualSublinesShortExact.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.iso_of_equal_sublines_shortExact : ∀ (X : Scheme.{0}) (V L Q L' Q' : X.Modules) (l : L ⟶ V) (m : V ⟶ Q) (w : l ≫ m = 0) (l' : L' ⟶ V) (m' : V ⟶ Q') (w' : l' ≫ m' = 0), (ShortComplex.mk l m w).ShortExact → (ShortComplex.mk l' m' w').ShortExact → IsVB Q 1 → IsVB Q' 1 → l' ≫ m = 0 → ∃ e : L' ≅ L, e.hom ≫ l = l' := by
  first | exact @GlobalTheory.SameLine.eq_line | exact GlobalTheory.SameLine.eq_line | (intros; apply GlobalTheory.SameLine.eq_line <;> assumption)
