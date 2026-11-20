import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnOfCharts
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralFundSetInterLe

namespace GlobalTheory.MetricWeightTest

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
The claim follows from `fundSet_holds r X x0 ho (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X)`.
-/
theorem exists_fundSet_orth {x0 : Frame X.Ψ r} (ho : IsOrth X x0) : ∃ FF, IsFundSet X x0 FF :=
  fundSet_holds r X x0 ho (GlobalTheory.ClosedDiscontinuity.propDisc_closed r X)

/- English proof (translation)
Introduce `h`. Establish `hae : ∀ᵐ z ∂muF X x0, False`. Rewrite using `[ae_iff]`. Simplify using `using h`. Unfold `muF at hae`.

Rewrite `hae` using `[ae_withDensity_iff (OntoC.measurable_densF X x0), ae_restrict_iff' (OntoB.isOpen_OmF X x0).measurableSet]`. Establish `h0 : (volume : Measure (V (nd X))) (OmF X x0) = 0`. Rewrite using `[measure_eq_zero_iff_ae_notMem]`. Use `filter_upwards [hae] with z hz hzO`. Conclude with `hz hzO (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact OntoB.densF_pos hzO)`.

Conclude with `((OntoB.isOpen_OmF X x0).measure_pos volume ⟨0, IW.zero_mem_OmF X x0 ho⟩).ne' h0`.
-/
theorem muF_ne_zero {x0 : Frame X.Ψ r} (ho : IsOrth X x0) : muF X x0 Set.univ ≠ 0 := by
  intro h
  have hae : ∀ᵐ z ∂muF X x0, False := by
    rw [ae_iff]; simpa using h
  unfold muF at hae
  rw [ae_withDensity_iff (OntoC.measurable_densF X x0),
    ae_restrict_iff' (OntoB.isOpen_OmF X x0).measurableSet] at hae
  have h0 : (volume : Measure (V (nd X))) (OmF X x0) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with z hz hzO
    exact hz hzO (by rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact OntoB.densF_pos hzO)
  exact ((OntoB.isOpen_OmF X x0).measure_pos volume ⟨0, IW.zero_mem_OmF X x0 ho⟩).ne' h0

/- English proof (translation)
Introduce `h`. Establish `e` using `GlobalTheory.Unfold.lintegral_unfold GlobalTheory.FrameMeasureClosed.measInv_holds r X x0 ho FF hF (fun _ => 1) measurable_const (fun _ _ _ _ => rfl)`. Rewrite `e` using `[setLIntegral_measure_zero _ _ h, lintegral_one]`. Conclude with `muF_ne_zero X ho e`.
-/
theorem fundSet_pos {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hF : IsFundSet X x0 FF) : muF X x0 FF ≠ 0 := by
  intro h
  have e := GlobalTheory.Unfold.lintegral_unfold GlobalTheory.FrameMeasureClosed.measInv_holds r X x0 ho FF hF
    (fun _ => 1) measurable_const (fun _ _ _ _ => rfl)
  rw [setLIntegral_measure_zero _ _ h, lintegral_one] at e
  exact muF_ne_zero X ho e

end GlobalTheory.MetricWeightTest
