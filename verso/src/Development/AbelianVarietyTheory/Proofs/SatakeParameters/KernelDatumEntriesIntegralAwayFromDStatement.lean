import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumEntriesIntegralAwayFromD
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FKernelDatumEntriesIntegralAwayFromD.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.jetIntegralityBis_ofKer_of_hyp : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → 3 ≤ D.host.splitBound → ∀ ep be sg, OrbitPlaces.JetIntegralityBis (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  first | exact @GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d | exact GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d | (intros; apply GlobalTheory.Ggeo.AdmEntInt.kernelDatum_entries_integral_away_from_d <;> assumption)
