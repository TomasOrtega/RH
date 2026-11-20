import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurveJacobian
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCurvePointDVR
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.JacobianAtCurvePoint
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Introduce `σ _ I w hI hint hdim hw`. Take `⟨hd, hdvr⟩` from `hDVR σ I w hI hint hdim hw`. Set `: Algebra (JacobianAtCurvePoint.ptLoc w) (pointLocalRing I w)` to `inferInstanceAs (Algebra (JacobianAtCurvePoint.ptLoc w) (JacobianAtCurvePoint.ptQuot I w))`. Establish `: IsScalarTower (MvPolynomial σ ℂ) (JacobianAtCurvePoint.ptLoc w) (pointLocalRing I w)` using `inferInstanceAs (IsScalarTower (MvPolynomial σ ℂ) (JacobianAtCurvePoint.ptLoc w) (JacobianAtCurvePoint.ptQuot I w))`. Conclude with `JacobianAtCurvePoint.exists_of_isDiscreteValuationRing I w hw (pointLocalRing I w) (by exact Ideal.Quotient.mk_surjective) (by exact Ideal.mk_ker)`.
-/
theorem NormalCurveJacobian.proof (hDVR : NormalCurvePointDVR.Statement) : NormalCurveJacobian.Statement := by
  intro σ _ I w hI hint hdim hw
  obtain ⟨hd, hdvr⟩ := hDVR σ I w hI hint hdim hw
  let : Algebra (JacobianAtCurvePoint.ptLoc w) (pointLocalRing I w) :=
    inferInstanceAs (Algebra (JacobianAtCurvePoint.ptLoc w) (JacobianAtCurvePoint.ptQuot I w))
  have : IsScalarTower (MvPolynomial σ ℂ) (JacobianAtCurvePoint.ptLoc w) (pointLocalRing I w) :=
    inferInstanceAs
      (IsScalarTower (MvPolynomial σ ℂ) (JacobianAtCurvePoint.ptLoc w) (JacobianAtCurvePoint.ptQuot I w))
  exact JacobianAtCurvePoint.exists_of_isDiscreteValuationRing I w hw (pointLocalRing I w)
    (by exact Ideal.Quotient.mk_surjective) (by exact Ideal.mk_ker)

end

end GroundTheory.Heights₂.Heights
