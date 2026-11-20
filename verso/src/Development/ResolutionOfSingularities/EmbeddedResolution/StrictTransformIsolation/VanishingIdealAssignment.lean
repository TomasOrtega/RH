import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.RestrictionToOpens
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction

noncomputable def vanishingIdealAssignment : VanishingAssignment.{u} :=
  fun _ T => Scheme.IdealSheafData.vanishingIdeal T

/- English proof (authored)
The assignment sends each closed subset to its vanishing ideal sheaf by definition. Evaluating it at the indicated scheme and subset gives that sheaf.
-/
theorem vanishingIdealAssignment_apply (X : Scheme.{u}) (T : Closeds ↥X) :
    vanishingIdealAssignment X T = Scheme.IdealSheafData.vanishingIdeal T := rfl

def VanishingOrderOneOnSmoothDivisor : Prop :=
  ∀ (k : Type u) [Field k] (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of k))
    (U : W.Opens) (D : (U.toScheme).IdealSheafData),
    IsSmoothDivisor (U.ι ≫ p) D →
    ∀ (T : Closeds ↥(D.subscheme)) (y : ↥(D.subscheme)),
      IsGenericPoint y (T : Set ↥(D.subscheme)) →
      (T : Set ↥(D.subscheme)) ∉ irreducibleComponents ↥(D.subscheme) →
      orderAt (vanishingIdealAssignment D.subscheme T) y = 1

def AgreeNearVanishingComapSubscheme : Prop :=
  ∀ (W : Scheme.{u}) (N : W.IdealSheafData) (U : W.Opens)
    (H : (U.toScheme).IdealSheafData) (T : Closeds ↥W) (S : Closeds ↥(H.subscheme))
    (x : ↥(H.subscheme)),
    (S : Set ↥(H.subscheme)) = (H.subschemeι ≫ U.ι).base ⁻¹' (T : Set ↥W) →
    (U.ι.base ⁻¹' (T : Set ↥W)) ⊆ (H.support : Set ↥(U.toScheme)) →
    AgreeNear N (vanishingIdealAssignment W T) ((H.subschemeι ≫ U.ι).base x) →
    AgreeNear ((N.comap U.ι).comap H.subschemeι) (vanishingIdealAssignment H.subscheme S) x

def VanishingComapOpens : Prop :=
  ∀ (W : Scheme.{u}) (T : Closeds ↥W) (V : W.Opens) (S : Closeds ↥(V.toScheme)),
    (S : Set ↥(V.toScheme)) = V.ι.base ⁻¹' (T : Set ↥W) →
    (vanishingIdealAssignment W T).comap V.ι = vanishingIdealAssignment V.toScheme S

def OrderAtEqOfAgreeNear : Prop :=
  ∀ (W : Scheme.{u}) (I J : W.IdealSheafData) (x : ↥W),
    AgreeNear I J x → orderAt I x = orderAt J x

/- English proof (authored)
The inclusion of the smaller open factors through the larger open. Pull back the given equality on the larger open along this factor map. Composition of pullbacks identifies the resulting ideals with the restrictions to the smaller open.
-/
private theorem comap_opens_eq_of_le {W : Scheme.{u}} {I J : W.IdealSheafData} {U U' : W.Opens}
    (h : U' ≤ U) (hEq : I.comap U.ι = J.comap U.ι) :
    I.comap U'.ι = J.comap U'.ι := by
  have hι : W.homOfLE h ≫ U.ι = U'.ι := by simp
  rw [← hι, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, hEq]

/- English proof (authored)
Choose a neighborhood of the image point on which the two ideals agree. Its inverse image is a neighborhood of the original point. The inverse-image square identifies the restriction of each pulled-back ideal with the pullback of its restriction on the chosen neighborhood. Those restrictions agree, so the pulled-back ideals agree near the original point.
-/
theorem agreeNear_comap_ι (W : Scheme.{u}) (V : W.Opens) (I J : W.IdealSheafData)
    (y : ↥(V.toScheme)) (h : AgreeNear I J (V.ι.base y)) :
    AgreeNear (I.comap V.ι) (J.comap V.ι) y := by
  obtain ⟨U, hU, hEq⟩ := (agreeNear_iff I J (V.ι.base y)).mp h
  refine (agreeNear_iff _ _ _).mpr ⟨V.ι ⁻¹ᵁ U, hU, ?_⟩
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    ← morphismRestrict_ι V.ι U, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_comp, hEq]

/- English proof (authored)
The stalk map of the open immersion is an isomorphism. It identifies the original ideal stalk with the pulled-back ideal stalk and preserves the powers of the maximal ideal. Hence the orders agree.
-/
theorem orderAt_comap_ι (W : Scheme.{u}) (V : W.Opens) (I : W.IdealSheafData)
    (y : ↥(V.toScheme)) :
    orderAt (I.comap V.ι) y = orderAt I (V.ι.base y) :=
  FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isOpenImmersion V.ι I y

/- English proof (authored)
Take a neighborhood of the given point where the two ideal restrictions agree, and consider the corresponding point of the open subscheme. Order is preserved under the open inclusion for both ideals. The equal restrictions have equal order at that point, giving the original equality.
-/
theorem orderAtEqOfAgreeNear : OrderAtEqOfAgreeNear.{u} := by
  intro W I J x h
  obtain ⟨U, hxU, hEq⟩ := (agreeNear_iff I J x).mp h
  obtain ⟨y, hy⟩ : ∃ y : ↥(U.toScheme), U.ι.base y = x := by
    have hx : x ∈ Set.range ⇑U.ι.base := by simpa using hxU
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy⟩
  rw [← hy, ← orderAt_comap_ι W U I y, ← orderAt_comap_ι W U J y, hEq]

/- English proof (authored)
Use the supplied results for order one on a smooth divisor, restriction of local vanishing ideals to a closed subscheme and an open, and equality of order under local agreement. Local agreement is transitive because two witnessing neighborhoods can be intersected and the equalities restricted there. Pullback preserves local agreement, ideal products, and order along open inclusions by the corresponding identities. The remaining conditions follow from the descriptions of open and closed subscheme inclusions, the support formulas for products and vanishing ideals, and the definitions of locally open sets and nonvanishing on components. These facts supply the geometry hypotheses for the vanishing ideal assignment.
-/
theorem idealSheafGeometryHypotheses_of_orderAtEqOfAgreeNear
    (h1 : VanishingOrderOneOnSmoothDivisor.{u}) (h2 : AgreeNearVanishingComapSubscheme.{u})
    (h3 : VanishingComapOpens.{u}) (h4 : OrderAtEqOfAgreeNear.{u}) :
    IdealSheafGeometryHypotheses vanishingIdealAssignment.{u} :=
  { agreeNear_comap := agreeNear_comap_ι
    agreeNear_trans := by
      intro W I J K x hIJ hJK
      obtain ⟨U1, hx1, e1⟩ := (agreeNear_iff I J x).mp hIJ
      obtain ⟨U2, hx2, e2⟩ := (agreeNear_iff J K x).mp hJK
      exact (agreeNear_iff I K x).mpr
        ⟨U1 ⊓ U2, ⟨hx1, hx2⟩,
          (comap_opens_eq_of_le inf_le_left e1).trans (comap_opens_eq_of_le inf_le_right e2)⟩
    comap_mul := fun W X f I J => Scheme.IdealSheafData.comap_mul I J f
    base_comp := fun X Y Z f g x => by simp
    isClosed_support := fun W I => I.support.isClosed
    isClosedEmbedding_subschemeι := fun W I =>
      IsClosedImmersion.isClosedEmbedding (f := I.subschemeι)
    isEmbedding_ι := fun W U => U.ι.isOpenEmbedding.toIsEmbedding
    isOpen_opens := fun W U => U.2
    orderAt_comap := orderAt_comap_ι
    orderAt_congr := h4
    orderAt_vanishing_eq_one := h1
    range_ι := fun W U => by simp
    range_subschemeι := fun W I => by simp
    support_mul := fun W I J => by
      rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup]
    not_subset_support_of_nonzeroOnComponents := fun W I h => (nonzeroOnComponents_iff I).mp h
    support_vanishing := fun W T => by simp [vanishingIdealAssignment]
    top_mul := fun W I => by simp
    agreeNear_vanishing_restrict := h2
    comap_vanishing := h3 }

/- English proof (authored)
Order equality under local agreement has already been proved for any two ideal sheaves. Combine it with the three supplied vanishing-ideal properties in the construction of the geometry hypotheses.
-/
theorem idealSheafGeometryHypotheses_of_vanishingOrderOneOnSmoothDivisor
    (h1 : VanishingOrderOneOnSmoothDivisor.{u}) (h2 : AgreeNearVanishingComapSubscheme.{u})
    (h3 : VanishingComapOpens.{u}) :
    IdealSheafGeometryHypotheses vanishingIdealAssignment.{u} :=
  idealSheafGeometryHypotheses_of_orderAtEqOfAgreeNear h1 h2 h3 orderAtEqOfAgreeNear

end FunctorialResolution.EmbeddedResolution.OpenImmersionRestriction
