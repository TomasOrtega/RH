import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfChartPointSecPointSpecChart
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartPointTrdeg
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecPointSeparable
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChart
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenericFormsKer
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PDerivSpanTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

/- English proof (translation)
The claim follows from `GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof) GroundTheory.Heig …`.
-/
private theorem coneDim₃ : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof
    (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof)
    GroundTheory.Heights₂.Heights.IncIdealPrime.full

/- English proof (translation)
The claim follows from `ChartPointTrdeg.proof coneDim₃ GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof`.
-/
theorem ChartPointTrdeg.full : ChartPointTrdeg.Statement :=
  ChartPointTrdeg.proof coneDim₃ GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof
/- English proof (translation)
The claim follows from `SpecChart.proof`.
-/
theorem SpecChart.full : SpecChart.Statement := SpecChart.proof
/- English proof (translation)
The claim follows from `GenericFormsKer.proof`.
-/
theorem GenericFormsKer.full : GenericFormsKer.Statement := GenericFormsKer.proof
/- English proof (translation)
The claim follows from `DerivSpanTrdeg.proof`.
-/
theorem DerivSpanTrdeg.full : DerivSpanTrdeg.Statement := DerivSpanTrdeg.proof

/- English proof (translation)
The claim follows from `SecPointSeparable.proof GenericFormsKer.full DerivSpanTrdeg.full h`.
-/
theorem SecPointSeparable.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    SecPointSeparable.Statement :=
  SecPointSeparable.proof GenericFormsKer.full DerivSpanTrdeg.full h

/- English proof (translation)
The claim follows from `GenSecSeparable.proof SecAlgFinite.full GenSecDomain.full ChartPointTrdeg.full (SecPointSeparable.of_freeParAlgIndep h)`.
-/
theorem GenSecSeparable.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    GenSecSeparable.Statement :=
  GenSecSeparable.proof SecAlgFinite.full GenSecDomain.full ChartPointTrdeg.full
    (SecPointSeparable.of_freeParAlgIndep h)

/- English proof (translation)
Establish `cnf : ChowNormForm.Statement` using `ChowNormForm.proof (ChowNormFormGeneric.proof SecAlgFinite.full GenSecDomain.full (GenSecSeparable.of_freeParAlgIndep h) ChowSecDvd.full NormFormIrreducible.full GenChowIrreducible.full NormFormDvd.full) SecAlgFieldChange.full`. Establish `nzd : SecLinNZD.Statement` using `SecLinNZD.proof cnf NormFormEval.full SpecFirstNeField.full`. Conclude with `SpecLength.proof SpecChart.full FiniteOrd.full ParDVRIsDVR.full SecBFinite.full (SecBLinInj.proof SecBGeneric.full SecBTorsionFree.full nzd ParAlgIndep.full)`.
-/
theorem SpecLength.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) : SpecLength.Statement := by
  have cnf : ChowNormForm.Statement :=
    ChowNormForm.proof
      (ChowNormFormGeneric.proof SecAlgFinite.full GenSecDomain.full (GenSecSeparable.of_freeParAlgIndep h)
        ChowSecDvd.full NormFormIrreducible.full GenChowIrreducible.full NormFormDvd.full)
      SecAlgFieldChange.full
  have nzd : SecLinNZD.Statement := SecLinNZD.proof cnf NormFormEval.full SpecFirstNeField.full
  exact SpecLength.proof SpecChart.full FiniteOrd.full ParDVRIsDVR.full SecBFinite.full
    (SecBLinInj.proof SecBGeneric.full SecBTorsionFree.full nzd ParAlgIndep.full)

/- English proof (translation)
The claim follows from `ChowFormSectionVertical.of_chartPoint_secPoint_specChart ChartPointTrdeg.full (SecPointSeparable.of_freeParAlgIndep h) SpecChart.full`.
-/
theorem ChowFormSectionVertical.of_freeParAlgIndep (h : FreeParAlgIndep.Statement) :
    ChowFormSectionVertical.Statement :=
  ChowFormSectionVertical.of_chartPoint_secPoint_specChart ChartPointTrdeg.full
    (SecPointSeparable.of_freeParAlgIndep h) SpecChart.full

end GroundTheory.Heights₂.Heights.Vertical
