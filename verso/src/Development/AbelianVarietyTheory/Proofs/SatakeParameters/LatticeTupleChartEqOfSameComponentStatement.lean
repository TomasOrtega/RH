import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTupleChartEqOfSameComponent
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLatticeTupleChartEqOfSameComponent.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.latticeTuple_chart_eq_of_same_component : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ j (hj : j ≤ D.R.m) (c : (sysS H X std).Lv.comp j) (La Lb : ((sysS H X std).Pj j).Tup), ((sysS H X std).Pj j).IsLatTup La → ((sysS H X std).Pj j).IsLatTup Lb → J.chart std j hj (c, La) = J.chart std j hj (c, Lb)) := by
  first | exact @GlobalTheory.TwV.Xc.chart_eq_of_comp | exact GlobalTheory.TwV.Xc.chart_eq_of_comp | (intros; apply GlobalTheory.TwV.Xc.chart_eq_of_comp <;> assumption)
