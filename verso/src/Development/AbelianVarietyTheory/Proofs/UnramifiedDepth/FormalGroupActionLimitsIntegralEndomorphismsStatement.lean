import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupActionLimitsIntegralEndomorphisms
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ActLimit.limit_endomorphisms` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FFormalGroupActionLimitsIntegralEndomorphisms.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.formalGroupAction_limits_integral_endomorphisms : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd), EndomorphismLimitIntegral Y := by
  first | exact @GlobalTheory.ActLimit.limit_endomorphisms | exact GlobalTheory.ActLimit.limit_endomorphisms | (intros; apply GlobalTheory.ActLimit.limit_endomorphisms <;> assumption)
