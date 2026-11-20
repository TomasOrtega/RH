import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericSections
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsPullbackFaithful
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadBundle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem SpreadHomInj.proof (h₁ : GenericSectionsInj.Statement)
    (h₂ : PullbackFaithful.Statement.{0}) : SpreadHomInj.Statement := by
  intro X f _ _ a ha F G hF hG
  obtain ⟨m, hm, H⟩ := h₁ X f
  refine ⟨m, hm, fun n hn hmn ψ₁ ψ₂ e => ?_⟩
  have hk : IsUnit (((a : ℤ) * n : ℤ) : ℚ) := isUnit_intCast_rat _ (by positivity)
  have hG' : IsVectorBundle
      ((Scheme.Modules.pullback (X.homOfLE (invOpen_mul_le_left f a n))).obj G) :=
    hG.pullback_of_isOpenImmersion _
  refine h₂ _ _ (toInvOpen f ℚ ((a : ℤ) * n) hk)
    (H _ hk (Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr hmn) _)) _ _ hG' ψ₁ ψ₂ ?_
  unfold pullbackHomAlong at e
  rwa [cancel_epi, cancel_mono] at e

end GroundTheory.Heights₂.Heights.Model
