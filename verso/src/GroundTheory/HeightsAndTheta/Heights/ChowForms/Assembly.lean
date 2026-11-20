import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PFGNullstellensatz
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PProjNullstellensatz
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncidenceGeneric
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealPrime
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormMultiHomog
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PGenericLinearTrdeg
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealDim
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimOfChowForm
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PMinimalPrimeHomog
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimComponent
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormExists
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PLengthQuotientDet
import GroundTheory.HeightsAndTheta.Heights.ChowForms.POrdPolynomialLocalization
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormBirational
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PSectionOrder
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
The claim follows from `FGNullstellensatz.proof`.
-/
theorem FGNullstellensatz.full : FGNullstellensatz.Statement :=
  FGNullstellensatz.proof

/- English proof (translation)
The claim follows from `ProjNullstellensatz.proof FGNullstellensatz.full`.
-/
theorem ProjNullstellensatz.full : ProjNullstellensatz.Statement :=
  ProjNullstellensatz.proof FGNullstellensatz.full

/- English proof (translation)
The claim follows from `IncidenceGeneric.proof FGNullstellensatz.full`.
-/
theorem IncidenceGeneric.full : IncidenceGeneric.Statement :=
  IncidenceGeneric.proof FGNullstellensatz.full

/- English proof (translation)
The claim follows from `IncIdealPrime.proof IncidenceGeneric.full`.
-/
theorem IncIdealPrime.full : IncIdealPrime.Statement :=
  IncIdealPrime.proof IncidenceGeneric.full

/- English proof (translation)
The claim follows from `ChowFormMultiHomog.proof ProjNullstellensatz.full`.
-/
theorem ChowFormMultiHomog.full : ChowFormMultiHomog.Statement :=
  ChowFormMultiHomog.proof ProjNullstellensatz.full

/- English proof (translation)
The claim follows from `GenericLinearTrdeg.proof`.
-/
theorem GenericLinearTrdeg.full : GenericLinearTrdeg.Statement :=
  GenericLinearTrdeg.proof

/- English proof (translation)
The claim follows from `MinimalPrimeHomog.proof`.
-/
theorem MinimalPrimeHomog.full : MinimalPrimeHomog.Statement :=
  MinimalPrimeHomog.proof

/- English proof (translation)
The claim follows from `ConeDimComponent.proof MinimalPrimeHomog.full`.
-/
theorem ConeDimComponent.full : ConeDimComponent.Statement :=
  ConeDimComponent.proof MinimalPrimeHomog.full

/- English proof (translation)
The claim follows from `LengthQuotientDet.proof`.
-/
theorem LengthQuotientDet.full : LengthQuotientDet.Statement :=
  LengthQuotientDet.proof

/- English proof (translation)
The claim follows from `OrdPolynomialLocalization.proof`.
-/
theorem OrdPolynomialLocalization.full : OrdPolynomialLocalization.Statement :=
  OrdPolynomialLocalization.proof

/- English proof (translation)
The claim follows from `ChowFormBirational.proof IncidenceGeneric.full ChowFormMultiHomog.full`.
-/
theorem ChowFormBirational.full : ChowFormBirational.Statement :=
  ChowFormBirational.proof IncidenceGeneric.full ChowFormMultiHomog.full

/- English proof (translation)
The claim follows from `IncIdealDim.proof IncidenceGeneric.full GenericLinearTrdeg.full hA`.
-/
theorem IncIdealDim.of_affineChartTrdeg (hA : AffineChartTrdeg.Statement) :
    IncIdealDim.Statement :=
  IncIdealDim.proof IncidenceGeneric.full GenericLinearTrdeg.full hA

/- English proof (translation)
The claim follows from `ConeDimOfChowForm.proof (IncIdealDim.of_affineChartTrdeg hA) IncIdealPrime.full`.
-/
theorem ConeDimOfChowForm.of_affineChartTrdeg (hA : AffineChartTrdeg.Statement) :
    ConeDimOfChowForm.Statement :=
  ConeDimOfChowForm.proof (IncIdealDim.of_affineChartTrdeg hA) IncIdealPrime.full

/- English proof (translation)
The claim follows from `ChowFormExists.proof (IncIdealDim.of_affineChartTrdeg hA) IncIdealPrime.full`.
-/
theorem ChowFormExists.of_affineChartTrdeg (hA : AffineChartTrdeg.Statement) :
    ChowFormExists.Statement :=
  ChowFormExists.proof (IncIdealDim.of_affineChartTrdeg hA) IncIdealPrime.full

end GroundTheory.Heights₂.Heights
