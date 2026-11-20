import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthContentBoundProof
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FSplitPrimeDepthContentBoundProof.lean&line=162#L162)
-/
theorem _root_.GlobalTheory.T.splitPrimeDepthContentBound_proof : SplitBd := by
  first | exact @GlobalTheory.GoodDepth.splitBd | exact GlobalTheory.GoodDepth.splitBd | (intros; apply GlobalTheory.GoodDepth.splitBd <;> assumption)
