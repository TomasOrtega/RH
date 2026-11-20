import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagBundleProjVectorBundle
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFlagBundleProjVectorBundle.lean&line=317#L317)
-/
theorem _root_.GlobalTheory.T.exists_flag_bundle_proj_vector_bundle : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (B : Scheme.{0}) (q : B ⟶ Sp k) (E : B.Modules) (r : ℕ), IsProjOver q → GlobalTheory.VB.IsVB E r → ∃ (Y : Scheme.{0}) (π : Y ⟶ B) (fl : ∀ _ : Unit, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback π).obj E) r), GlobalTheory.CovTest.IsFlagBundle π (fun _ : Unit => E) (fun _ => r) fl ∧ IsProjOver (π ≫ q) := by
  first | exact @GlobalTheory.LineQuot.exists_isFlagBundle_isProjOver | exact GlobalTheory.LineQuot.exists_isFlagBundle_isProjOver | (intros; apply GlobalTheory.LineQuot.exists_isFlagBundle_isProjOver <;> assumption)
