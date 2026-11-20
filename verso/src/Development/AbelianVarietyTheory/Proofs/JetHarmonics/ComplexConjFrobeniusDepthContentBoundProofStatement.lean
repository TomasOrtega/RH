import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexConjFrobeniusDepthContentBoundProof
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GoodDepth.ConjPkg.phiCBd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FComplexConjFrobeniusDepthContentBoundProof.lean&line=362#L362)
-/
theorem _root_.GlobalTheory.T.complexConjFrobeniusDepthContentBound_proof : PhiCBd := by
  first | exact @GlobalTheory.GoodDepth.ConjPkg.phiCBd | exact GlobalTheory.GoodDepth.ConjPkg.phiCBd | (intros; apply GlobalTheory.GoodDepth.ConjPkg.phiCBd <;> assumption)
