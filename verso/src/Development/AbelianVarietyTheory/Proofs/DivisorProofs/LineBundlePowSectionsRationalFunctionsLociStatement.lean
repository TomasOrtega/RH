import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundlePowSectionsRationalFunctionsLoci
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HSAmp.pow_sec_dict` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLineBundlePowSectionsRationalFunctionsLoci.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.lineBundlePow_sections_rationalFunctions_loci : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ e : ℕ, (∀ u : (lbPow P.L.B e).Sec, ∃ f ∈ P.H e 0, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u) ∧ ∀ f ∈ P.H e 0, ∃ u : (lbPow P.L.B e).Sec, NV P e 0 f = ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus u := by
  first | exact @GlobalTheory.HSAmp.pow_sec_dict | exact GlobalTheory.HSAmp.pow_sec_dict | (intros; apply GlobalTheory.HSAmp.pow_sec_dict <;> assumption)
