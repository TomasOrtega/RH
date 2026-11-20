import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovTop.Sizes.hostN` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHostBoundHolds.lean&line=110#L110)
-/
theorem _root_.GlobalTheory.T.host_bound_holds : ∀ M : ℝ, HostN M := by
  first | exact @GlobalTheory.CovTop.Sizes.hostN | exact GlobalTheory.CovTop.Sizes.hostN | (intros; apply GlobalTheory.CovTop.Sizes.hostN <;> assumption)
