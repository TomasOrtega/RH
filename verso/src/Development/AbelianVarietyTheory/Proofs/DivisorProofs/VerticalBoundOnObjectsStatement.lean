import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VerticalBoundOnObjects
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.VertObj.vertBd_onObj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVerticalBoundOnObjects.lean&line=536#L536)
-/
theorem _root_.GlobalTheory.T.vertical_bound_on_objects : Hypotheses2 → HypothesesH → OnObj fun _ _ _ T _ _ => VertBd T := by
  first | exact @GlobalTheory.VertObj.vertBd_onObj | exact GlobalTheory.VertObj.vertBd_onObj | (intros; apply GlobalTheory.VertObj.vertBd_onObj <;> assumption)
