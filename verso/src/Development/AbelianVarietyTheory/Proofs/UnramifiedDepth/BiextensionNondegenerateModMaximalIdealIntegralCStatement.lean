import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BiextensionNondegenerateModMaximalIdealIntegralC
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnramifiedDepth%2FBiextensionNondegenerateModMaximalIdealIntegralC.lean&line=173#L173)
-/
theorem _root_.GlobalTheory.T.biextension_nondegenerate_mod_maximalIdeal_integral_chart : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) [StarRing (NumberField.RingOfIntegers E)], NondegenerateCharts Xo c := by
  first | exact @GlobalTheory.AlphaPair.ndg_at_chart | exact GlobalTheory.AlphaPair.ndg_at_chart | (intros; apply GlobalTheory.AlphaPair.ndg_at_chart <;> assumption)
