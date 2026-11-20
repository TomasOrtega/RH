import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietySmoothOverRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPtGenMat
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open CategoryTheory.Limits

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFlagVarietySmoothOverRat.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.flag_variety_smooth_over_rat : ∀ (ι : Type) [Fintype ι] (N : ℕ), SmoothOfRelativeDimension (dimFl ι N) (pullback.snd (GlobalTheory.FlagZ.flStr ι N) (spMap (algebraMap ℤ ℚ))) := by
  first | exact @GlobalTheory.FlagQ.smoothOfRelativeDimension_genericFibre | exact GlobalTheory.FlagQ.smoothOfRelativeDimension_genericFibre | (intros; apply GlobalTheory.FlagQ.smoothOfRelativeDimension_genericFibre <;> assumption)
