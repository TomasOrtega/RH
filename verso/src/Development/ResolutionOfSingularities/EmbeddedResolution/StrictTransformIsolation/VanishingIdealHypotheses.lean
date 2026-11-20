import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.OpenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.SmoothOrderOneCenters
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.RestrictionToOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealGeometry
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealAssignment
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealOrderOne
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CertificateOpenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace OpenImmersionRestriction

/- English proof (authored)
The assignment is the vanishing ideal sheaf. Pullback along an open immersion takes the vanishing ideal of a closed subset to the vanishing ideal of its inverse image. Apply this to the given open inclusion.
-/
theorem vanishingComapOpens : VanishingComapOpens.{u} := by
  intro W T U T' hT'
  simp only [vanishingIdealAssignment_apply]
  exact comap_vanishingIdeal_of_isOpenImmersion U.ι T T' hT'

/- English proof (authored)
The vanishing ideal assignment has order one at the required generic points of a smooth divisor, preserves local vanishing agreement under restriction to a closed subscheme, and commutes with restriction to opens. Apply the construction of the geometry hypotheses from these three properties.
-/
theorem idealSheafGeometryHypotheses_vanishingIdealAssignment : IdealSheafGeometryHypotheses (vanishingIdealAssignment.{u}) :=
  idealSheafGeometryHypotheses_of_vanishingOrderOneOnSmoothDivisor vanishingOrderOneOnSmoothDivisor agreeNearVanishingComapSubscheme vanishingComapOpens

/- English proof (authored)
Replace the assignment by the ordinary vanishing ideal. Smoothness of the ambient scheme and the vanishing subscheme, together with the absence of any entire ambient component in the closed subset, give order one at each point of the subset by the smooth vanishing-ideal theorem.
-/
private theorem orderAt_vanishingIdealAssignment_eq_one :
    ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)), Smooth p →
      ∀ T : Closeds ↥W, IsIrreducible (T : Set ↥W) →
      Smooth ((vanishingIdealAssignment W T).subschemeι ≫ p) →
      (∀ E ∈ irreducibleComponents ↥W, ¬ E ⊆ (T : Set ↥W)) →
      ∀ x ∈ (T : Set ↥W), FunctorialResolution.EmbeddedResolution.orderAt (vanishingIdealAssignment W T) x = 1 := by
  intro k _ _ W p hp T hirr hsm hcomp x hx
  rw [vanishingIdealAssignment_apply] at hsm ⊢
  exact orderAt_vanishingIdeal_eq_one p hp T hirr hsm hcomp x hx

/- English proof (authored)
An open immersion is smooth, so its composite with the given smooth structural morphism is smooth.
-/
private theorem smooth_opens_ι_comp_of_smooth :
    ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens), Smooth p → Smooth (U.ι ≫ p) := by
  intro k _ _ W p U hp
  have : Smooth p := hp
  infer_instance

/- English proof (authored)
Identify the assignments with the ordinary vanishing ideals. The closed subset on the divisor is the inverse image of the original subset, which lies in the divisor on the chosen open. The smooth restriction theorem for vanishing ideals along a smooth divisor gives smoothness of its vanishing subscheme over the field.
-/
private theorem smooth_vanishingIdealAssignment_of_isSmoothDivisor :
    ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (H : (U.toScheme).IdealSheafData),
      IsSmoothDivisor (U.ι ≫ p) H →
      ∀ (T : Closeds ↥W) (S : Closeds ↥(H.subscheme)),
        (S : Set ↥(H.subscheme)) = (H.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W) →
        (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme)) →
        Smooth ((vanishingIdealAssignment W T).subschemeι ≫ p) →
        Smooth ((vanishingIdealAssignment H.subscheme S).subschemeι ≫ (H.subschemeι ≫ (U.ι ≫ p))) := by
  intro k _ _ W p U H hH T S hS hTsubH hT
  rw [vanishingIdealAssignment_apply] at hT ⊢
  exact smooth_vanishingIdeal_comap_subschemeι p U H hH T S hS hTsubH hT

/- English proof (authored)
Pullback of the vanishing ideal to the open equals the vanishing ideal of the inverse-image closed subset. The corresponding pulled-back subscheme is the open restriction of the original smooth subscheme, so it stays smooth over the field. The ideal equality gives the asserted smoothness.
-/
private theorem smooth_vanishingIdealAssignment_restrict_opens :
    ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens) (T : Closeds ↥W)
      (S : Closeds ↥(U.toScheme)),
      (S : Set ↥(U.toScheme)) = U.ι.base ⁻¹' (T : Set ↥W) →
      Smooth ((vanishingIdealAssignment W T).subschemeι ≫ p) →
      Smooth ((vanishingIdealAssignment U.toScheme S).subschemeι ≫ (U.ι ≫ p)) := by
  intro k _ _ W p U T S hS hT
  rw [vanishingIdealAssignment_apply] at hT ⊢
  exact smooth_subschemeι_comp_of_eq (U.ι ≫ p)
    (comap_vanishingIdeal_of_isOpenImmersion U.ι T S hS).symm
    (smooth_comap_subschemeι_of_isOpenImmersion U.ι
      (Scheme.IdealSheafData.vanishingIdeal T) p hT)

/- English proof (authored)
The order-one theorem for the vanishing ideal gives the required order condition. Smoothness of an open restriction and the smoothness results for the vanishing ideals on a divisor and on an open supply the three smoothness conditions.
-/
theorem smoothVanishingHypotheses_vanishingIdealAssignment : SmoothVanishingHypotheses (vanishingIdealAssignment.{u}) where
  orderAt_vanishing_eq_one := orderAt_vanishingIdealAssignment_eq_one
  smooth_opens_ι_comp := smooth_opens_ι_comp_of_smooth
  smooth_vanishing_hypersurface := smooth_vanishingIdealAssignment_of_isSmoothDivisor
  smooth_vanishing_opens := smooth_vanishingIdealAssignment_restrict_opens

/- English proof (authored)
The vanishing ideal assignment satisfies both the ideal-sheaf geometry and the smooth-vanishing hypotheses. Applying the isolation theorem for a principalization certificate with these hypotheses proves the claim.
-/
theorem smoothOrderOneCentersIsolated_vanishingIdealAssignment_of_principalizationCertificate {k : Type u} [Field k] [CharZero k]
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    SmoothOrderOneCentersIsolated (vanishingIdealAssignment.{u}) W p I m Mem Z :=
  smoothOrderOneCentersIsolated_of_principalizationCertificate idealSheafGeometryHypotheses_vanishingIdealAssignment smoothVanishingHypotheses_vanishingIdealAssignment h

end OpenImmersionRestriction

/- English proof (authored)
Pullback along an open immersion preserves nonvanishing on components. The induced map from the pulled-back closed subscheme is an open immersion, and pullback of a smooth divisor remains a smooth divisor. These three results give the required stability.
-/
theorem openImmersionStability (k : Type u) [Field k] : OpenImmersionStability.{u} k := by
  refine ⟨?_, ?_, ?_⟩
  · intro V W f hf J hJ
    have : IsOpenImmersion f := hf
    exact NonzeroOnComponents.comap_of_isOpenImmersion hJ f
  · intro V W f hf D
    have : IsOpenImmersion f := hf
    exact OpenImmersionRestriction.isOpenImmersion_subschemeMap f D (comapSubscheme f D) (comapSubscheme_comp f D)
  · intro V W f hf p D hD
    have : IsOpenImmersion f := hf
    exact OpenImmersionRestriction.isSmoothDivisor_comap f p D hD

/- English proof (authored)
Apply the certificate pullback theorem with the established stability under open immersions. It gives the certificate for the pulled-back ideals and the inverse image of the boundary under the composed structural morphism.
-/
theorem PrincipalizationCertificate.comap_of_isOpenImmersion {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) {V : Scheme.{u}} (f : V ⟶ W)
    [IsOpenImmersion f] :
    PrincipalizationCertificate V (f ≫ p) (I.comap f) m (f.base ⁻¹' Mem) (Z.comap f) :=
  h.comap_of_openImmersionStability (openImmersionStability k) f

end FunctorialResolution.EmbeddedResolution

end
