import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureChartApply
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Mix.part_apply` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMixedChernFormSignedPartMeasureChartApply.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.mixedChernFormSignedPartMeasure_chart_apply : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) [SecondCountableTopology (CxPts p σ)] (D : ℕ) (L : Fin D → MLine p σ) (ε : ℤˣ) (c : AlgChart p σ D) (S : Set (CxPts p σ)), MeasurableSet S → S ⊆ c.e.source → part L ε S = ∫⁻ v in c.e '' S, ENNReal.ofReal ((ε : ℤ) * dens L c (c.e.symm v)) := by
  first | exact @GlobalTheory.Mix.part_apply | exact GlobalTheory.Mix.part_apply | (intros; apply GlobalTheory.Mix.part_apply <;> assumption)
