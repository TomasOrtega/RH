import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOverFieldHasFlag
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Vert.Flag.nonempty_of_field` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVectorBundleOverFieldHasFlag.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.vector_bundle_over_field_has_flag : ∀ (K : Type) [Field K] (E : (Spec (CommRingCat.of K)).Modules) (n : ℕ), GlobalTheory.VB.IsVB E n → Nonempty (Vert.Flag E n) := by
  first | exact @GlobalTheory.Vert.Flag.nonempty_of_field | exact GlobalTheory.Vert.Flag.nonempty_of_field | (intros; apply GlobalTheory.Vert.Flag.nonempty_of_field <;> assumption)
