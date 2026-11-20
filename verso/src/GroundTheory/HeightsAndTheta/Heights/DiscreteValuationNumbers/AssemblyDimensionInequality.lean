import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialPrimeOverZeroHeight
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PQuotientHeightAddOne
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPolynomialDimensionInequality
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimensionInequalityOneGenerator
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDimensionInequality
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PReesAlgebraDim
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PBlowUpModel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

/- English proof (translation)
The claim follows from `PolynomialDimensionInequality.proof PolynomialPrimeOverZeroHeight.proof.{u}`.
-/
theorem PolynomialDimensionInequality.full : PolynomialDimensionInequality.Statement.{u} :=
  PolynomialDimensionInequality.proof PolynomialPrimeOverZeroHeight.proof.{u}

/- English proof (translation)
The claim follows from `DimensionInequalityOneGenerator.proof PolynomialDimensionInequality.full.{u} QuotientHeightAddOne.proof.{u}`.
-/
theorem DimensionInequalityOneGenerator.full : DimensionInequalityOneGenerator.Statement.{u, v} :=
  DimensionInequalityOneGenerator.proof PolynomialDimensionInequality.full.{u}
    QuotientHeightAddOne.proof.{u}

/- English proof (translation)
The claim follows from `DimensionInequality.proof DimensionInequalityOneGenerator.full.{u, v} DimensionInequalityOneGenerator.full.{v, v}`.
-/
theorem DimensionInequality.full : DimensionInequality.Statement.{u, v} :=
  DimensionInequality.proof DimensionInequalityOneGenerator.full.{u, v}
    DimensionInequalityOneGenerator.full.{v, v}

/- English proof (translation)
The claim follows from `ReesAlgebraDim.proof DimensionInequality.full.{u, u}`.
-/
theorem ReesAlgebraDim.full : ReesAlgebraDim.Statement.{u} :=
  ReesAlgebraDim.proof DimensionInequality.full.{u, u}

/- English proof (translation)
The claim follows from `BlowUpModel.proof ReesAlgebraDim.full.{u}`.
-/
theorem BlowUpModel.full : BlowUpModel.Statement.{u} :=
  BlowUpModel.proof ReesAlgebraDim.full.{u}

end GroundTheory.Heights₂.Heights.NumbersDVR
