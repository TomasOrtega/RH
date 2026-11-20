import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalizationCoverOfPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitting
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.ArLieBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AffCover.exists_span_top_basicOpen_cover` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLocalizationCoverOfPoint.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_localization_cover_of_point : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (x : Sp K ⟶ X) {ι : Type} (V : ι → X.Opens), (∀ p : Sp K, ∃ i, p ∈ x ⁻¹ᵁ V i) → ∃ s : Set K, Ideal.span s = ⊤ ∧ ∀ a : s, ∃ i, ⊤ ≤ (spMap (algebraMap K (Localization.Away (a : K))) ≫ x) ⁻¹ᵁ V i := by
  first | exact @GlobalTheory.AffCover.exists_span_top_basicOpen_cover | exact GlobalTheory.AffCover.exists_span_top_basicOpen_cover | (intros; apply GlobalTheory.AffCover.exists_span_top_basicOpen_cover <;> assumption)
