import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetOfBlockTriangularInjective
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetMulStrictLowerEqOne
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DifferentiableAtAdjugate
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ChangeDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLeOfSection
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralImageLeConst
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetBorSat

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.FrameMeasureClosed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kapGG_holds : KapGGStatement (E := E) :=
  GlobalTheory.UnitriJac.kapGG_of_det GlobalTheory.det_conj_strictLower GlobalTheory.det_mul_strictLower_eq_one

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem measInv_holds : MeasInvStatement (E := E) :=
  GlobalTheory.measInv_of_jacobian kapGG_holds GlobalTheory.NormFactor.nfac_transform

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem frameMeas_holds : FrameMeasStatement (E := E) :=
  GlobalTheory.FrameMeas.frameMeas_of_local measInv_holds
    (GlobalTheory.frame_measure_local GlobalTheory.FrameSplit.frameSplit)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem extF_holds : ExtFStatement (E := E) :=
  extF_of lu_holds frameMeas_holds

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem measure_statements :
    (KapGGStatement (E := E)) ∧ (MeasInvStatement (E := E)) ∧ (FrameMeasStatement (E := E)) ∧
      (ExtFStatement (E := E)) :=
  ⟨kapGG_holds, measInv_holds, frameMeas_holds, extF_holds⟩

end GlobalTheory.FrameMeasureClosed
