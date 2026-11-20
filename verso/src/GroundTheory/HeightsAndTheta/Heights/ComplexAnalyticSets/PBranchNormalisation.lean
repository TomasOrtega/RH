import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchGermDimOne
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSameOrderBranchesMeet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceHasBranch
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdDeterminesPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveResidueDegree
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StOrdFiniteNonZeroDivisor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem BranchNormalisation.proof (h₀ : BranchGermDimOne.Statement) (h₁ : BranchPlace.Statement)
    (h₂ : SameOrderBranchesMeet.Statement) (h₃ : PlaceHasBranch.Statement)
    (h₄ : OrdDeterminesPlace.Statement) (h₅ : CurveResidueDegree.Statement)
    (h₆ : OrdFiniteNonZeroDivisor.Statement) : BranchNormalisation.Statement := by
  intro n I q m c hrad hm hcov hdisj
  have hdim := h₀ n I q m c hm hcov
  refine ⟨hdim, fun f hf ↦ h₆ n I q f hrad hdim fun P ↦ ?_, ?_⟩
  · obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj P
    rw [hb f]
    exact hf b
  choose P hP using fun b ↦ h₁ n I q (c b) hrad hdim

  have hcongr : ∀ Q Q' : MaximalSpectrum (curveNormalisation I q), Q = Q' → ∀ f : MvPolynomial (Fin n) ℂ,
      Ring.ord (Localization.AtPrime Q.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
      Ring.ord (Localization.AtPrime Q'.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime Q'.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) := by
    rintro Q _ rfl f
    rfl
  have hinj : Function.Injective P := by
    intro b b' hbb
    by_contra hne
    obtain ⟨x, hx, hxq⟩ := h₂ n I q (c b) (c b') hrad hdim fun f ↦
      (hP b f).symm.trans ((hcongr _ _ hbb f).trans (hP b' f))
    exact hxq (hdisj b b' hne hx)
  have hsurj : Function.Surjective P := by
    intro Q
    obtain ⟨b, hb⟩ := h₃ n I q m c hrad hdim hcov hdisj Q
    exact ⟨b, h₄ n I q hrad hdim (P b) Q fun f ↦ (hP b f).trans (hb f).symm⟩
  exact ⟨Equiv.ofBijective P ⟨hinj, hsurj⟩, fun b ↦ ⟨h₅ n I q hrad hdim (P b), hP b⟩⟩

end GroundTheory.Heights₂.Heights
