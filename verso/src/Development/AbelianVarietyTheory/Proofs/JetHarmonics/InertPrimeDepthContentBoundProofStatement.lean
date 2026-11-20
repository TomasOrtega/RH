import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthContentBoundProof
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertContent.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FInertPrimeDepthContentBoundProof.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.inertPrimeDepthContentBound_proof : InertBd := by
  first | exact @GlobalTheory.InertContent.main | exact GlobalTheory.InertContent.main | (intros; apply GlobalTheory.InertContent.main <;> assumption)
