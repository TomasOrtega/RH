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
Introduce `n k J A O g hJ hO hg hZ hA`. Break down `O.eq_empty_or_nonempty with rfl | hne` into its components or cases. Conclude with `differentiableOn_empty`. Establish `hsurj : ∀ y ∈ O, ∃ x ∈ zeroLocus J, A *ᵥ x = y` using `fun y hy => ⟨g y, hZ y hy, hA y hy⟩`. Use `choose Q D hD0 hQ hQ' using hP n k J A O hJ hO hne hsurj`.

Establish `hP0 : (∏ j, D j) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun j _ => hD0 j`. Rewrite using `[differentiableOn_pi]`. Introduce `j`. Establish `hcont : ContinuousOn (fun y => g y j) O` using `(continuous_apply j).comp_continuousOn hg`. Use `hE k (∏ j, D j) O (fun y => g y j) hP0 hO hcont ?_` and prove the remaining obligations.

Introduce and unpack `y ⟨hy, hPy⟩`. Establish `hyx : A *ᵥ g y = y` using `hA y hy`. Establish `hDj : eval y (D j) ≠ 0`. Introduce `h0`. Apply `hPy` to reduce the goal to its premises.

Use `show eval y (∏ i, D i) = 0`. Rewrite using `[map_prod]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ j) h0`. Establish `hroot : ∀ t ∈ O, eval (Fin.cons (g t j) t : Fin (k + 1) → ℂ) (Q j) = 0`. Introduce `t ht`.

Establish `h` using `hQ j (g t) (hZ t ht)`. Rewrite `h` using `[hA t ht]`. Then use the resulting hypothesis. Establish `hder : eval (Fin.cons (g y j) y : Fin (k + 1) → ℂ) (pderiv 0 (Q j)) ≠ 0`. Establish `h` using `hQ' j (g y) (hZ y hy) (by rwa [hyx])`. Rewrite `h` using `[hyx]`. Then use the resulting hypothesis.

Conclude with `(hR k (Q j) O (fun t => g t j) hO hcont hroot y hy hder).differentiableWithinAt`.
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
