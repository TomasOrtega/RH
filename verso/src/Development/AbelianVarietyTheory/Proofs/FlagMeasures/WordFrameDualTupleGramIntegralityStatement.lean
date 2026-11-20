import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WordFrameDualTupleGramIntegrality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Direct
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CovDom.frame_dual_lat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FWordFrameDualTupleGramIntegrality.lean&line=165#L165)
-/
theorem _root_.GlobalTheory.T.wordFrame_dualTuple_gram_integrality : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word), GlobalTheory.SgAlg.IsFrame (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (algebraMap D.host.F D.host.E (Tc u)) (Pc X u) ∧ GlobalTheory.SgAlg.IsDual (D.sp.cm.sig : D.host.E →+* D.host.E) (Jc X) (Pc X u) (fc X) ∧ GlobalTheory.SnMass.tupLat (GlobalTheory.SnMass.id1 D.host.E D.R.rS) (GlobalTheory.SnMass.sideM (Pc X u) (fc X)) ≤ Lc X := by
  first | exact @GlobalTheory.CovDom.frame_dual_lat | exact GlobalTheory.CovDom.frame_dual_lat | (intros; apply GlobalTheory.CovDom.frame_dual_lat <;> assumption)
