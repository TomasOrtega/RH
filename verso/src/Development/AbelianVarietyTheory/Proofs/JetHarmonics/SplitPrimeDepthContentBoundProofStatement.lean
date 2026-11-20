import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthContentBoundProof
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.GoodDepth.splitBd | exact GlobalTheory.GoodDepth.splitBd | (intros; apply GlobalTheory.GoodDepth.splitBd <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.splitPrimeDepthContentBound_proof : SplitBd := by
  first | exact @GlobalTheory.GoodDepth.splitBd | exact GlobalTheory.GoodDepth.splitBd | (intros; apply GlobalTheory.GoodDepth.splitBd <;> assumption)
