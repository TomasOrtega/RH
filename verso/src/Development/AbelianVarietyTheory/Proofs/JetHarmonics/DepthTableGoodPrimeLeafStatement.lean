import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimeLeaf
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodDepth.leafGood` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FDepthTableGoodPrimeLeaf.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.depthTable_goodPrimeLeaf : LeafGoodSt := by
  first | exact @GlobalTheory.GoodDepth.leafGood | exact GlobalTheory.GoodDepth.leafGood | (intros; apply GlobalTheory.GoodDepth.leafGood <;> assumption)
