import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConsStatementOfPrismatic
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConsStatementOfPrismatic.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.cons_statement_of_prismatic : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ConsSt := by
  first | exact @GlobalTheory.ConsNumber.main | exact GlobalTheory.ConsNumber.main | (intros; apply GlobalTheory.ConsNumber.main <;> assumption)
