import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PUnipotentLeadingMinor
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PUnipotentCoordinates
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PPluckerFrameChange
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGramSumOfMinors
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.POmitStepPolynomial
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PLineQuotientDeterminant
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSectionLocalEquation
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PDiagonalQuotient
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PDiagonalLocalDVR
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PBlochOverlap
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSectionNormLog
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGKernelIdentity
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PMixedCoefficient
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereHeightUniform
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereMoment
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibrePushforward
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalKernel
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PSphereLongitudeCoordinates
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalHeightReduction
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalKernelPairing
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PZonalBilinearFormula
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PGHatIdentity
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreConstantClosedForm
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PFibreIntegralInvariant
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PCompactPairCurveForm
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PBarCurveForm
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PTorusInvariantDiagonal
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PTopPowerDiagonal
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.PPolarisationDegreeD
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UnipotentLeadingMinor.full : UnipotentLeadingMinor.Statement :=
  UnipotentLeadingMinor.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PluckerFrameChange.full : PluckerFrameChange.Statement :=
  PluckerFrameChange.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GramSumOfMinors.full : GramSumOfMinors.Statement :=
  GramSumOfMinors.proof PluckerFrameChange.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem OmitStepPolynomial.full : OmitStepPolynomial.Statement :=
  OmitStepPolynomial.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LineQuotientDeterminant.full : LineQuotientDeterminant.Statement :=
  LineQuotientDeterminant.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SectionLocalEquation.full : SectionLocalEquation.Statement :=
  SectionLocalEquation.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DiagonalQuotient.full : DiagonalQuotient.Statement :=
  DiagonalQuotient.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DiagonalLocalDVR.full : DiagonalLocalDVR.Statement :=
  DiagonalLocalDVR.proof DiagonalQuotient.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BlochOverlap.full : BlochOverlap.Statement :=
  BlochOverlap.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SectionNormLog.full : SectionNormLog.Statement :=
  SectionNormLog.proof BlochOverlap.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GKernelIdentity.full : GKernelIdentity.Statement :=
  GKernelIdentity.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem MixedCoefficient.full : MixedCoefficient.Statement :=
  MixedCoefficient.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ZonalKernel.full : ZonalKernel.Statement :=
  ZonalKernel.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SphereLongitudeCoordinates.full : SphereLongitudeCoordinates.Statement :=
  SphereLongitudeCoordinates.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ZonalHeightReduction.full : ZonalHeightReduction.Statement :=
  ZonalHeightReduction.proof SphereLongitudeCoordinates.full ZonalKernel.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ZonalKernelPairing.full : ZonalKernelPairing.Statement :=
  ZonalKernelPairing.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ZonalBilinearFormula.full : ZonalBilinearFormula.Statement :=
  ZonalBilinearFormula.proof ZonalHeightReduction.full ZonalKernelPairing.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GHatIdentity.full : GHatIdentity.Statement :=
  GHatIdentity.proof GKernelIdentity.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FibreConstantClosedForm.full : FibreConstantClosedForm.Statement :=
  FibreConstantClosedForm.proof ZonalBilinearFormula.full GHatIdentity.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fibreConstant_eq (k : ℕ) :
    fibreConstant k = -(1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1) :=
  FibreConstantClosedForm.full.1 k

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FibreIntegralInvariant.full : FibreIntegralInvariant.Statement :=
  FibreIntegralInvariant.proof FibreConstantClosedForm.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CompactPairCurveForm.full : CompactPairCurveForm.Statement :=
  CompactPairCurveForm.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BarCurveForm.full : BarCurveForm.Statement :=
  BarCurveForm.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TorusInvariantDiagonal.full : TorusInvariantDiagonal.Statement :=
  TorusInvariantDiagonal.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TopPowerDiagonal.full : TopPowerDiagonal.Statement :=
  TopPowerDiagonal.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PolarisationDegreeD.full : PolarisationDegreeD.Statement :=
  PolarisationDegreeD.proof

end GroundTheory.Heights₂.Heights.FlagBundles
