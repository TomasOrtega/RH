import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StContinuousSectionHolomorphic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRiemannExtensionPolynomial
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StContinuousRootHolomorphic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjectionCoordinateEquation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Matrix

noncomputable section

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem ContinuousSectionHolomorphic.proof (hP : ProjectionCoordinateEquation.Statement)
    (hR : ContinuousRootHolomorphic.Statement) (hE : RiemannExtensionPolynomial.Statement) :
    ContinuousSectionHolomorphic.Statement := by
  intro n k J A O g hJ hO hg hZ hA
  rcases O.eq_empty_or_nonempty with rfl | hne
  · exact differentiableOn_empty
  have hsurj : ∀ y ∈ O, ∃ x ∈ zeroLocus J, A *ᵥ x = y := fun y hy => ⟨g y, hZ y hy, hA y hy⟩
  choose Q D hD0 hQ hQ' using hP n k J A O hJ hO hne hsurj
  have hP0 : (∏ j, D j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hD0 j
  rw [differentiableOn_pi]
  intro j
  have hcont : ContinuousOn (fun y => g y j) O := (continuous_apply j).comp_continuousOn hg
  refine hE k (∏ j, D j) O (fun y => g y j) hP0 hO hcont ?_
  rintro y ⟨hy, hPy⟩
  have hyx : A *ᵥ g y = y := hA y hy
  have hDj : eval y (D j) ≠ 0 := by
    intro h0
    apply hPy
    show eval y (∏ i, D i) = 0
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) h0
  have hroot : ∀ t ∈ O, eval (Fin.cons (g t j) t : Fin (k + 1) → ℂ) (Q j) = 0 := by
    intro t ht
    have h := hQ j (g t) (hZ t ht)
    rwa [hA t ht] at h
  have hder : eval (Fin.cons (g y j) y : Fin (k + 1) → ℂ) (pderiv 0 (Q j)) ≠ 0 := by
    have h := hQ' j (g y) (hZ y hy) (by rwa [hyx])
    rwa [hyx] at h
  exact (hR k (Q j) O (fun t => g t j) hO hcont hroot y hy hder).differentiableWithinAt

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
