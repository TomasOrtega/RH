import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StJacobianPrimeDerivations
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolyDerivationsDetectSquare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCotangentBasisInPrime
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StDerivationMinorOfDetection
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGeneratorsClearDenominators
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem JacobianPrimeDerivations.proof (hDetect : PolyDerivationsDetectSquare.Statement)
    (hBasis : CotangentBasisInPrime.Statement) (hMinor : DerivationMinorOfDetection.Statement)
    (hClear : LocalGeneratorsClearDenominators.Statement) : JacobianPrimeDerivations.Statement := by
  intro k _ n p hp
  obtain ⟨h, f, hfp, hspan, hind⟩ := hBasis (MvPolynomial (Fin n) k) p
  obtain ⟨D, hD⟩ := hMinor (MvPolynomial (Fin n) k) p h f hfp hind
    (fun g hg hDg => hDetect k n p g hg hDg)
  obtain ⟨s, hs, hsp⟩ := hClear (MvPolynomial (Fin n) k) p h f hfp hspan
  exact ⟨h, f, D, s, hfp, hs, hsp, hD⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
