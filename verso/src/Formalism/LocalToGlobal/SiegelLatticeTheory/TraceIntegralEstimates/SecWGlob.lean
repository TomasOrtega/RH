import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.SecWSec
import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSD
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyInst

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.S.Pv.SecW

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D X u u' sc hsc`. Establish `hk : 0 < D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Set `i0 : Fin D.R.k` to `⟨0, hk⟩`. Use `choose w Fw using fun v => Formalism.L2.S.Pv.HaarSubS.frm_at X u v`. Use `choose w' Fw' using fun v => Formalism.L2.S.Pv.HaarSubS.frm_at X u' v`.

Establish `hdim : ∀ v, X.B.I.n = 2 * D.R.rS + 1 + D.R.k` using `fun v => (ProductExactness.frameLoc_X X u u v).dim`. Establish `hT : 0 < Tw (D` using `D) u := ProductExactness.Tw_pos u`. Establish `hT' : 0 < Tw (D` using `D) u' := ProductExactness.Tw_pos u'`. Use `⟨fun c v => secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0 (c v), ?_, ?_⟩` and prove the remaining obligations. Conclude with `measurable_pi_lambda _ fun v => (measurable_secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0).comp (measurable_pi_apply v)`.

Introduce `c hc v`. Establish `hcv` using `hc v`. Establish `hg` using `ProductExactness.normSq_last_sub_pos_of_Gv_diagonal_pos (Tw (D := D) u) (Tw (D := D) u') (c v) hcv.2`. Conclude with `zhat_secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0 hcv.1 hg`.
-/
theorem stepSection_holds : Formalism.L2.SG.RealObj.EnergyInst.StepSection := by
  intro D X u u' sc hsc
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  let i0 : Fin D.R.k := ⟨0, hk⟩
  choose w Fw using fun v => Formalism.L2.S.Pv.HaarSubS.frm_at X u v
  choose w' Fw' using fun v => Formalism.L2.S.Pv.HaarSubS.frm_at X u' v
  have hdim : ∀ v, X.B.I.n = 2 * D.R.rS + 1 + D.R.k := fun v => (ProductExactness.frameLoc_X X u u v).dim
  have hT : 0 < Tw (D := D) u := ProductExactness.Tw_pos u
  have hT' : 0 < Tw (D := D) u' := ProductExactness.Tw_pos u'
  refine ⟨fun c v => secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0 (c v), ?_, ?_⟩
  · exact measurable_pi_lambda _ fun v => (measurable_secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0).comp
      (measurable_pi_apply v)
  · intro c hc v
    have hcv := hc v
    have hg := ProductExactness.normSq_last_sub_pos_of_Gv_diagonal_pos (Tw (D := D) u) (Tw (D := D) u') (c v) hcv.2
    exact zhat_secV (Fw v) (Fw' v) (hdim v) hT hT' hsc i0 hcv.1 hg

end Formalism.L2.S.Pv.SecW
