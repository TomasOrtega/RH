import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometry
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IteratedStrictTransformPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactFunctoriality

/- English proof (authored)
For a length-zero upper sequence it suffices to show that every lower center pulls back to the unit ideal along any comparison to its stage over the base. Suppose an upper point mapped to a lower center support. Projecting to the original scheme would give a point of the original marked order locus, since every center projects into it. Over the base this image is also the image of the upper point under the smooth morphism. Smooth pullback identifies the upper marked order locus with the inverse image of the original one, so the upper point would belong to the assumed empty locus. Thus all these pulled-back center supports are empty, and the comparison with the length-zero sequence follows.
-/
theorem isPullback_of_orderAtLeastLocus_comap_eq_empty
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
    (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T)
    (Y : Scheme.{u}) (φ : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth φ]
    (n : SequenceOfBlowups Y) (hn : n.length = 0)
    (hempty : orderAtLeastLocus (T.ideal.comap φ) T.mult = (∅ : Set ↥Y)) :
    IsPullbackBlowupSequence φ n (maxContactPrincipalization hinv A T).toSequenceOfBlowups := by
  have : CharZero T.base := h.valid.charZero
  have : AlgebraicGeometry.Smooth T.structMap := h.valid.smooth
  refine isPullback_of_length_zero_of_comap_center_eq_top φ n
    (maxContactPrincipalization hinv A T).toSequenceOfBlowups hn ?_
  intro i hi ψ hψ
  refine Blowup.comap_eq_top_of_notMem_support ψ ((maxContactPrincipalization hinv A T).toSequenceOfBlowups.center i) ?_
  intro y hy
  have hmem : ((maxContactPrincipalization hinv A T).toSequenceOfBlowups.projectionToBase i).base (ψ.base y)
      ∈ orderAtLeastLocus T.ideal T.mult :=
    OrderReductionCorrectness.projectionToBase_mem_orderAtLeastLocus_of_mem_center T h.valid (maxContactPrincipalization hinv A T) i hi
      (ψ.base y) hy
  have hfy : φ.base y ∈ orderAtLeastLocus T.ideal T.mult := by
    have h1 : φ.base y
        = ((maxContactPrincipalization hinv A T).toSequenceOfBlowups.projectionToBase i).base (ψ.base y) := by
      rw [← hψ]
      rfl
    rw [h1]
    exact hmem
  have hcs := orderAtLeastLocus_comap T.base T.structMap φ T.ideal T.mult
  rw [hempty] at hcs
  have hy2 : y ∈ (∅ : Set ↥Y) := by
    rw [hcs]
    exact hfy
  exact hy2.elim

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
