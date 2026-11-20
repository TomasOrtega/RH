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

/- English proof (translation)
Introduce `W T U T' hT'`. Simplify using `only [vanishingIdealAssignment_apply]`. Conclude with `comap_vanishingIdeal_of_isOpenImmersion U.ι T T' hT'`.
-/
theorem vanishingComapOpens : VanishingComapOpens.{u} := by
  intro W T U T' hT'
  simp only [vanishingIdealAssignment_apply]
  exact comap_vanishingIdeal_of_isOpenImmersion U.ι T T' hT'

/- English proof (translation)
The claim follows from `idealSheafGeometryHypotheses_of_vanishingOrderOneOnSmoothDivisor vanishingOrderOneOnSmoothDivisor agreeNearVanishingComapSubscheme vanishingComapOpens`.
-/
theorem idealSheafGeometryHypotheses_vanishingIdealAssignment : IdealSheafGeometryHypotheses (vanishingIdealAssignment.{u}) :=
  idealSheafGeometryHypotheses_of_vanishingOrderOneOnSmoothDivisor vanishingOrderOneOnSmoothDivisor agreeNearVanishingComapSubscheme vanishingComapOpens

/- English proof (translation)
Introduce `k _ _ W p hp T hirr hsm hcomp x hx`. Rewrite `hsm`, the goal using `[vanishingIdealAssignment_apply]`. Conclude with `orderAt_vanishingIdeal_eq_one p hp T hirr hsm hcomp x hx`.
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

/- English proof (translation)
Introduce `k _ _ W p U hp`. Establish `: Smooth p` using `hp`. Use `infer_instance`.
-/
private theorem smooth_opens_ι_comp_of_smooth :
    ∀ (k : Type u) [Field k] [CharZero k] (W : Scheme.{u})
      (p : W ⟶ Spec (CommRingCat.of k)) (U : W.Opens), Smooth p → Smooth (U.ι ≫ p) := by
  intro k _ _ W p U hp
  have : Smooth p := hp
  infer_instance

/- English proof (translation)
Introduce `k _ _ W p U H hH T S hS hTsubH hT`. Rewrite `hT`, the goal using `[vanishingIdealAssignment_apply]`. Conclude with `smooth_vanishingIdeal_comap_subschemeι p U H hH T S hS hTsubH hT`.
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

/- English proof (translation)
Introduce `k _ _ W p U T S hS hT`. Rewrite `hT`, the goal using `[vanishingIdealAssignment_apply]`. Conclude with `smooth_subschemeι_comp_of_eq (U.ι ≫ p) (comap_vanishingIdeal_of_isOpenImmersion U.ι T S hS).symm (smooth_comap_subschemeι_of_isOpenImmersion U.ι (Scheme.IdealSheafData.vanishingIdeal T) p hT)`.
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

/- English proof (translation)
The claim follows from `orderAt_vanishingIdealAssignment_eq_one smooth_opens_ι_comp := smooth_opens_ι_comp_of_smooth smooth_vanishing_hypersurface := smooth_vanishingIdealAssignment_of_isSmoothDivisor smooth_vanishing_opens := smooth_vanishingIdealAssignment_restrict_opens`.
-/
theorem smoothVanishingHypotheses_vanishingIdealAssignment : SmoothVanishingHypotheses (vanishingIdealAssignment.{u}) where
  orderAt_vanishing_eq_one := orderAt_vanishingIdealAssignment_eq_one
  smooth_opens_ι_comp := smooth_opens_ι_comp_of_smooth
  smooth_vanishing_hypersurface := smooth_vanishingIdealAssignment_of_isSmoothDivisor
  smooth_vanishing_opens := smooth_vanishingIdealAssignment_restrict_opens

/- English proof (translation)
The claim follows from `smoothOrderOneCentersIsolated_of_principalizationCertificate idealSheafGeometryHypotheses_vanishingIdealAssignment smoothVanishingHypotheses_vanishingIdealAssignment h`.
-/
theorem smoothOrderOneCentersIsolated_vanishingIdealAssignment_of_principalizationCertificate {k : Type u} [Field k] [CharZero k]
    {W : Scheme.{u}} {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) :
    SmoothOrderOneCentersIsolated (vanishingIdealAssignment.{u}) W p I m Mem Z :=
  smoothOrderOneCentersIsolated_of_principalizationCertificate idealSheafGeometryHypotheses_vanishingIdealAssignment smoothVanishingHypotheses_vanishingIdealAssignment h

end OpenImmersionRestriction

/- English proof (translation)
Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `V W f hf J hJ`. Establish `: IsOpenImmersion f` using `hf`. Conclude with `NonzeroOnComponents.comap_of_isOpenImmersion hJ f`. Introduce `V W f hf D`.

Establish `: IsOpenImmersion f` using `hf`. Conclude with `OpenImmersionRestriction.isOpenImmersion_subschemeMap f D (comapSubscheme f D) (comapSubscheme_comp f D)`. Introduce `V W f hf p D hD`. Establish `: IsOpenImmersion f` using `hf`. Conclude with `OpenImmersionRestriction.isSmoothDivisor_comap f p D hD`.
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

/- English proof (translation)
The claim follows from `h.comap_of_openImmersionStability (openImmersionStability k) f`.
-/
theorem PrincipalizationCertificate.comap_of_isOpenImmersion {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {I : W.IdealSheafData} {m : ℕ} {Mem : Set ↥W}
    {Z : W.IdealSheafData} (h : PrincipalizationCertificate W p I m Mem Z) {V : Scheme.{u}} (f : V ⟶ W)
    [IsOpenImmersion f] :
    PrincipalizationCertificate V (f ≫ p) (I.comap f) m (f.base ⁻¹' Mem) (Z.comap f) :=
  h.comap_of_openImmersionStability (openImmersionStability k) f

end FunctorialResolution.EmbeddedResolution

end
