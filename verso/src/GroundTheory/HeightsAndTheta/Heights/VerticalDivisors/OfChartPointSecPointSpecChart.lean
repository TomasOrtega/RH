import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Assembly
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenSecSeparable
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFibreClosedComponent
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenSecKer
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFiniteOrd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

/- English proof (translation)
The claim follows from `FibreClosedComponent.proof`.
-/
theorem FibreClosedComponent.full : FibreClosedComponent.Statement := FibreClosedComponent.proof
/- English proof (translation)
The claim follows from `FiniteOrd.proof`.
-/
theorem FiniteOrd.full : FiniteOrd.Statement := FiniteOrd.proof
/- English proof (translation)
The claim follows from `FibreCompDim.proof FibreClosedComponent.full FibreCut.full GenericFibreDrop.full`.
-/
theorem FibreCompDim.full : FibreCompDim.Statement :=
  FibreCompDim.proof FibreClosedComponent.full FibreCut.full GenericFibreDrop.full

/- English proof (translation)
The claim follows from `GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof) GroundTheory.Heig …`.
-/
private theorem coneDim : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
  GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof
    (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof)
    GroundTheory.Heights₂.Heights.IncIdealPrime.full

/- English proof (translation)
The claim follows from `GroundTheory.Heights₂.Heights.ChowFormExists.proof (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof) GroundTheory.Heights …`.
-/
private theorem chowExists : GroundTheory.Heights₂.Heights.ChowFormExists.Statement :=
  GroundTheory.Heights₂.Heights.ChowFormExists.proof
    (GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof)
    GroundTheory.Heights₂.Heights.IncIdealPrime.full

/- English proof (translation)
The claim follows from `GenSecKer.proof SecAlgField.full coneDim`.
-/
theorem GenSecKer.full : GenSecKer.Statement := GenSecKer.proof SecAlgField.full coneDim
/- English proof (translation)
The claim follows from `SpecCompDim.proof coneDim FibreCompDim.full`.
-/
theorem SpecCompDim.full : SpecCompDim.Statement := SpecCompDim.proof coneDim FibreCompDim.full
/- English proof (translation)
The claim follows from `SecIdealOfPrime.proof SpecCompDim.full chowExists ResidueAlgIndep.full SecAlgField.full GenSecKer.full`.
-/
theorem SecIdealOfPrime.full : SecIdealOfPrime.Statement :=
  SecIdealOfPrime.proof SpecCompDim.full chowExists ResidueAlgIndep.full SecAlgField.full GenSecKer.full
/- English proof (translation)
The claim follows from `SpecMax.proof SecBFinite.full SecIdealOfPrime.full`.
-/
theorem SpecMax.full : SpecMax.Statement := SpecMax.proof SecBFinite.full SecIdealOfPrime.full

/- English proof (translation)
The claim follows from `ChowFormSectionVertical.of_remaining (GenSecSeparable.proof SecAlgFinite.full GenSecDomain.full hTrdeg hSep) FibreClosedComponent.full GenSecKer.full hChart FiniteOrd.full`.
-/
theorem ChowFormSectionVertical.of_chartPoint_secPoint_specChart
    (hTrdeg : ChartPointTrdeg.Statement) (hSep : SecPointSeparable.Statement)
    (hChart : SpecChart.Statement) : ChowFormSectionVertical.Statement :=
  ChowFormSectionVertical.of_remaining
    (GenSecSeparable.proof SecAlgFinite.full GenSecDomain.full hTrdeg hSep)
    FibreClosedComponent.full GenSecKer.full hChart FiniteOrd.full

end GroundTheory.Heights₂.Heights.Vertical
