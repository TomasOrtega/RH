import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.BlowupDerivativeIdealBound
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderUnderStalkIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupSeqComparison
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BlowupLiftCongruence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.WeakTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.RadicalCenterIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace OrderReductionCorrectness

/- English proof (authored)
Apply the blowup-lift comparison theorem. The controlled-transform product identity first gives equality of the two projected maps on the transformed subscheme. Around any point of that subscheme, both projected maps therefore land in a common affine neighborhood of their image. The affine lift comparison gives equality of the lifted maps on the corresponding open of the transformed subscheme. These opens cover it, so the lifted maps agree there.
-/
theorem blowupLiftEqOnControlledTransform : BlowupLiftEqOnControlledTransform.{u} := EmbeddedResolution.blowupLiftEqOnControlledTransform

/- English proof (authored)
The closed subscheme of the center is smooth over a field and hence reduced. Its defining ideal is radical. Containment of the center support in the other support puts the other ideal in the vanishing ideal of the center support. This vanishing ideal is the center's radical and therefore the center ideal itself.
-/
theorem le_of_support_subset_of_smooth : ∀ (k : Type u) [Field k] (X : Scheme.{u})
    (p : X ⟶ Spec (CommRingCat.of k)) (Z : X.IdealSheafData),
    AlgebraicGeometry.Smooth (Z.subschemeι ≫ p) →
    ∀ J : X.IdealSheafData,
      (((Z.support : Set ↥X)) ⊆ ((J.support : Set ↥X))) → J ≤ Z :=
  smoothSubschemeIdealIsRadical

/- English proof (authored)
The stage Noetherianity theorem applies to the marked sequence of the admissible triple at an index within its length. A Noetherian scheme is locally Noetherian, giving the property of the stage scheme.
-/
theorem isLocallyNoetherian_schemeAt : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i ≤ s.length → AlgebraicGeometry.IsLocallyNoetherian (s.schemeAt i) := by
  intro T hT s i hi
  have : AlgebraicGeometry.IsNoetherian (s.schemeAt i) :=
    MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT s i hi
  infer_instance

/- English proof (authored)
Identify the structural map upstairs with the composite through the smooth comparison. Derivative balancing is equivalent to the stated power containments for its iterated derivative ideals. Smooth pullback commutes with these iterated derivative ideals and preserves powers and inclusions. Pulling back each power containment downstairs thus gives the corresponding one upstairs, which proves derivative balancing.
-/
theorem isBalanced_comap_of_smooth : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
    ∀ [AlgebraicGeometry.LocallyOfFiniteType T.structMap]
      [AlgebraicGeometry.LocallyOfFiniteType q],
    IsDerivBalanced T.base T.structMap T.ideal T.mult →
    IsDerivBalanced T.base q (T.ideal.comap h) T.mult := by
  intro T hT Y q f _ hq _ _ hbal
  subst hq
  have : AlgebraicGeometry.Smooth T.structMap := hT.smooth
  refine isDerivBalanced_of_pow_le T.base (f ≫ T.structMap) ?_
  intro i hi
  rw [derivIdealSheafIterate_comap T.base T.structMap f i T.ideal,
    ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_pow]
  exact Scheme.IdealSheafData.comap_mono f (IsDerivBalanced.derivIdealSheafIterate_pow_le T.base T.structMap hbal hi)

/- English proof (authored)
The successor ideal is the controlled transform by its product identity and uniqueness. Apply the derivative transform bound to the derivative iterate of order one below the mark. Since the mark is positive, the remaining exceptional exponent in the bound is one. This derivative iterate is the maximal-contact ideal, both before and after the blowup. The bound is exactly the desired maximal-contact inequality.
-/
theorem maxContactIdealComapLeControlled : MaxContactIdealComapLeControlled.{u} := by
  intro k _ _ X X₁ p _ _ π Z E hZ hπ _ _ _ A μ hμ hA A₁ hA₁
  have hct : A₁ = controlledTransform π Z A μ hπ hA :=
    eq_controlledTransform_of_mul_eq_comap π Z A μ hπ hA A₁ hA₁
  have key := comap_derivIdealSheafIterate_le_exceptionalIdeal_pow_mul k p π Z E hZ hπ A μ hA
    (μ - 1) (Nat.sub_le μ 1)
  have hsub : μ - (μ - 1) = 1 := by omega
  rw [hsub, pow_one] at key
  simp only [maxContactIdeal_eq_derivIdealSheafIterate]
  rw [hct]
  exact key

/- English proof (authored)
The maximal-contact ideal satisfies the one-step containment under controlled transform. The construction from this containment produces the sequence of maximal-contact controlled transforms, with the initial pullback, successive product identities and center containments.
-/
theorem existsMaxContactControlledTransforms : ExistsMaxContactControlledTransforms.{u} :=
  existsMaxContactControlledTransforms_of_comapLeControlled maxContactIdealComapLeControlled

/- English proof (authored)
Induct on the stage. At zero the ideal is pulled back along the initial isomorphism, and its marked order locus is the corresponding inverse image. At a successor the one-blowup order-locus result puts the image in the preceding marked order locus, using the controlled-transform identity and the center condition. Apply induction to that image and compose the projections to obtain membership in the original locus.
-/
theorem projectionToBase_mem_orderAtLeastLocus_of_mem_ideal :
    ∀ (T : MarkedIdealWithBoundary.{u}) (s : T.SequenceOfBlowups) (i : ℕ), i ≤ s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ orderAtLeastLocus (s.ideal i) T.mult →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult := by
  intro T s i
  induction i with
  | zero =>
      intro _ x hx
      rw [s.ideal_zero, orderAtLeastLocus_comap_iso_hom_eq_preimage] at hx
      rw [SequenceOfBlowups.projectionToBase_zero]
      exact hx
  | succ n ih =>
      intro hn x hx
      have hn' : n < s.length := hn
      have h1 : (s.transitionMapSucc n).base x ∈ orderAtLeastLocus (s.ideal n) T.mult :=
        OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf (s.transitionMapSucc n) (s.center n)
          (s.isBlowupAlongIdealSheaf_blowupMorphism n hn') (s.ideal n) (s.ideal (n + 1)) T.mult
          (s.ideal_succ n hn') (s.center_order n hn') hx
      have h2 := ih (le_of_lt hn') _ h1
      rw [MarkedSequenceOfBlowups.projectionToBase_succ_apply]
      exact h2

/- English proof (authored)
The center support is contained in the marked order locus at its stage. Apply the projection result for a point of this stage locus to conclude that its image lies in the original marked order locus.
-/
theorem projectionToBase_mem_orderAtLeastLocus_of_mem_center : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (s : T.SequenceOfBlowups) (i : ℕ),
    i < s.length → ∀ x : ↥(s.schemeAt i),
      x ∈ (((s.center i).support : Set ↥(s.schemeAt i))) →
      (s.projectionToBase i).base x ∈ orderAtLeastLocus T.ideal T.mult := by
  intro T hT s i hi x hx
  exact projectionToBase_mem_orderAtLeastLocus_of_mem_ideal T s i (le_of_lt hi) x (s.center_order i hi hx)

/- English proof (authored)
For each actual lower blowup choose a point in its center support. Its projection to the base lies in the image of the upper base map by hypothesis, so the pair lifts to the scheme pullback at that lower stage. The lift is in the support of the pulled-back center. Thus every lower center survives pullback. The strictness criterion for pullback sequences then matches all steps and gives a strict pullback.
-/
theorem isStrictPullback_of_isPullback_of_center_nonempty : ∀ (X' X : Scheme.{u}) (φ : X' ⟶ X) (s' : SequenceOfBlowups X')
    (s : SequenceOfBlowups X), IsPullbackBlowupSequence φ s' s →
    (∀ i : ℕ, i < s.length → (((s.center i).support : Set ↥(s.schemeAt i))).Nonempty) →
    (∀ i : ℕ, i < s.length → ∀ x ∈ (((s.center i).support : Set ↥(s.schemeAt i))),
      (s.projectionToBase i).base x ∈ Set.range φ.base) →
    IsStrictPullbackBlowupSeq φ s' s := by
  intro X' X φ s' s hpb hne hran
  exact hpb.isStrictPullback_of_support_comap_center_nonempty (support_comap_center_nonempty_of_mem_range φ s hne hran)

end OrderReductionCorrectness

end FunctorialResolution.EmbeddedResolution

end
