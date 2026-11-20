import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOnObjects
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNefOnObjects.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.nef_on_objects : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → OnObj fun _ _ A _ _ _ => NefAt A := by
  first | exact @GlobalTheory.NefAtObj.nefAt_onObj | exact GlobalTheory.NefAtObj.nefAt_onObj | (intros; apply GlobalTheory.NefAtObj.nefAt_onObj <;> assumption)
