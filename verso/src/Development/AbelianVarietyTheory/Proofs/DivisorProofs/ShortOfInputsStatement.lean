import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortOfInputs
import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovHt.ShortPf.short` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FShortOfInputs.lean&line=207#L207)
-/
theorem _root_.GlobalTheory.T.short_of_inputs : Hypotheses2 → DeepGood → Size → FlatDeg → Short := by
  first | exact @GlobalTheory.CovHt.ShortPf.short | exact GlobalTheory.CovHt.ShortPf.short | (intros; apply GlobalTheory.CovHt.ShortPf.short <;> assumption)
