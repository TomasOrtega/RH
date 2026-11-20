import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferFn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

/- English proof (translation)
Introduce `Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hg Y a b Φ`. Establish `hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π'` using `hA.1`. Establish `hz` using `hpl.2.1`. Establish `hz'` using `hpl.2.2.1`. Establish `hΦ : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'` using `Φ.2`.

Establish `hF : Gauge.FamR P Bs (fun _ => Qx8.Dp P.k P.r Bs.z Bs.z') (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))`. Use `⟨Qx5.isOpen_OpR P.k P.r Bs.z Bs.z', fun c _ => Qx8.Dp_dom P.k P.r Bs.z Bs.z', fun q => ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Gauge.GC.GT.sec_pt P Bs hpl q).1.2.2`. Conclude with `NFx1.TC.radSp_fam hΦ`. Introduce `c hc`.

Conclude with `Qx8.slice_FF hz hz' hΦ hc`. Establish `h` using `hg (fun _ => Qx8.Dp P.k P.r Bs.z Bs.z') (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) hF Y a b`. Use function extensionality and compare the values at `ρ`. Use `show MA.toSm P (Gauge.rawR P Bs.μsec e ((X.t (Y : ℂ) a b Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) = MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ')) ρ`. Use `Eq.trans ?_ (h ρ)` and prove the remaining obligations.

Use `congr 1`. Use function extensionality and compare the values at `q`. Unfold `Gauge.rawR`. Rewrite using `[X.t_apply (Y : ℂ) a b Φ _ (Gauge.GC.GT.sec_pt P Bs hpl q).1]`. Both sides reduce to the same expression.
-/
theorem quadratic_transfer_identity : GQBridge := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hg Y a b Φ
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hA.1
  have hz := hpl.2.1
  have hz' := hpl.2.2.1
  have hΦ : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := Φ.2
  have hF : Gauge.FamR P Bs (fun _ => Qx8.Dp P.k P.r Bs.z Bs.z') (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    refine ⟨Qx5.isOpen_OpR P.k P.r Bs.z Bs.z', fun c _ => Qx8.Dp_dom P.k P.r Bs.z Bs.z', fun q => ?_, ?_, ?_⟩
    · exact (Gauge.GC.GT.sec_pt P Bs hpl q).1.2.2
    · exact NFx1.TC.radSp_fam hΦ
    · intro c hc
      exact Qx8.slice_FF hz hz' hΦ hc
  have h := hg (fun _ => Qx8.Dp P.k P.r Bs.z Bs.z') (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) hF Y a b
  funext ρ
  show MA.toSm P (Gauge.rawR P Bs.μsec e ((X.t (Y : ℂ) a b Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) =
    MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ')) ρ
  refine Eq.trans ?_ (h ρ)
  congr 1
  funext q
  unfold Gauge.rawR
  rw [X.t_apply (Y : ℂ) a b Φ _ (Gauge.GC.GT.sec_pt P Bs hpl q).1]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
