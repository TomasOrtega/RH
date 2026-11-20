import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSeriesScalarBoundedOfPosPair
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwV.Xc.scal_of_pos_pair` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FThetaSeriesScalarBoundedOfPosPair.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.thetaSeries_scalar_bounded_of_pos_pair : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => S.Pos → S.Pair → S.Scal) := by
  first | exact @GlobalTheory.TwV.Xc.scal_of_pos_pair | exact GlobalTheory.TwV.Xc.scal_of_pos_pair | (intros; apply GlobalTheory.TwV.Xc.scal_of_pos_pair <;> assumption)
