import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MovedDatumEqOfLatticeTuplesAgreeAway
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwV.Xc.xiM_eq_of_sameAway` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FMovedDatumEqOfLatticeTuplesAgreeAway.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.movedDatum_eq_of_latticeTuples_agreeAway : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => ∀ v j (hj : j < D.R.m) (La Lb : (sysS H X std).Lt j) (La' Lb' : (sysS H X std).Lt (j + 1)), SameAway (hT := hT) (H := H) (X := X) std v j La Lb → SameAway (hT := hT) (H := H) (X := X) std v (j + 1) La' Lb' → GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j La La' = GlobalTheory.TwU.xiM (sysS H X std) (J.fd std) (J.xi0 std S.Xi) j Lb Lb') := by
  first | exact @GlobalTheory.TwV.Xc.xiM_eq_of_sameAway | exact GlobalTheory.TwV.Xc.xiM_eq_of_sameAway | (intros; apply GlobalTheory.TwV.Xc.xiM_eq_of_sameAway <;> assumption)
