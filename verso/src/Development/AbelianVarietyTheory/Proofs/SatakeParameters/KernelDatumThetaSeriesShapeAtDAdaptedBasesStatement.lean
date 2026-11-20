import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumThetaSeriesShapeAtDAdaptedBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaZJetsThree
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FKernelDatumThetaSeriesShapeAtDAdaptedBases.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.kernelDatum_thetaSeries_shape_at_d_adaptedBases : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.Hyp → t.Adapted → ∀ ep be sg, OrbitPlaces.ThetaKernelShapeAtD (OrbitPlaces.ofKer (nuRowOK D) t.ent ep be sg) Y := by
  first | exact @GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted | exact GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted | (intros; apply GlobalTheory.Ggeo.KerShapeD.thetaKernelShapeAtD_ofKer_of_hyp_adapted <;> assumption)
