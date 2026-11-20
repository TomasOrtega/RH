import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleFamilyAgreeingSmallExtensionTangStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothExistsPointLiftSquareZeroLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveLineBundleFamilyCalculusRulesStatement

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

/- English proof (translation)
Introduce `S _ A _ hA U _ M hM hI hT C _ _ e he hk s N hN u₀ h`. Establish `hsq : (Ideal.span {e}) ^ 2 = ⊥`. Rewrite using `[Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot, sq]`. Conclude with `hk e he`. Take `⟨v, hv, hp⟩` from `GlobalTheory.T.smooth_exists_point_lift_squareZero_localRing U.left S U.hom C (Ideal.span {e}) hsq s u₀.left (Over.w u₀)`.

Set `u' : Over.mk s ⟶ U` to `Over.homMk v hp`. Establish `hu : u₀ = ptMap s (Ideal.Quotient.mk (Ideal.span {e})) ≫ u'` using `by ext1`. Conclude with `hv.symm`. Distinguish the cases in `h0 : e = 0`. Establish `hb : Function.Bijective (Ideal.Quotient.mk (Ideal.span {e}))`.

Use `⟨?_, Ideal.Quotient.mk_surjective⟩` and prove the remaining obligations. Rewrite using `[RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_eq_bot]`. Conclude with `h0`. Establish `: IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e})))` using `(RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom`. Establish `: IsIso (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))).left` using `inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e})))))`.

Establish `: IsIso ((Over.forget S).map (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))))` using `this`. Establish `: IsIso (ptMap s (Ideal.Quotient.mk (Ideal.span {e})))` using `isIso_of_reflects_iso _ (Over.forget S)`. Establish `h'` using `(GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A).2.2.2.1 _ _ _ _ N M _ _ (inv (ptMap s (Ideal.Quotient.mk (Ideal.span {e})))) hN.isLB hM.isLB h`. Rewrite `h'` using `[IsIso.inv_hom_id]`. Conclude with `⟨_, h'⟩`.

Conclude with `GlobalTheory.T.exists_lineBundleFamily_agreeing_smallExtension_tangent S A hA U M hM hI hT C e he hk h0 s N hN u' (hu ▸ h)`.
-/
theorem smallLift_of_tanLift : ∀ (S : Scheme.{0}) [IsAffine S] (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (U : Over S) [Smooth U.hom] (M : LB (A ⊗ U).left), Fam A M → Inj A M → TanLift A M → SmallLift A M := by
  intro S _ A _ hA U _ M hM hI hT C _ _ e he hk s N hN u₀ h
  have hsq : (Ideal.span {e}) ^ 2 = ⊥ := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_bot, sq]
    exact hk e he
  obtain ⟨v, hv, hp⟩ := GlobalTheory.T.smooth_exists_point_lift_squareZero_localRing U.left S U.hom C (Ideal.span {e}) hsq s u₀.left (Over.w u₀)
  let u' : Over.mk s ⟶ U := Over.homMk v hp
  have hu : u₀ = ptMap s (Ideal.Quotient.mk (Ideal.span {e})) ≫ u' := by
    ext1
    exact hv.symm
  by_cases h0 : e = 0
  · have hb : Function.Bijective (Ideal.Quotient.mk (Ideal.span {e})) := by
      refine ⟨?_, Ideal.Quotient.mk_surjective⟩
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, Ideal.span_singleton_eq_bot]
      exact h0
    have : IsIso (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e}))) :=
      (RingEquiv.ofBijective _ hb).toCommRingCatIso.isIso_hom
    have : IsIso (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))).left :=
      inferInstanceAs (IsIso (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {e})))))
    have : IsIso ((Over.forget S).map (ptMap s (Ideal.Quotient.mk (Ideal.span {e})))) := this
    have : IsIso (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))) := isIso_of_reflects_iso _ (Over.forget S)
    have h' := (GlobalTheory.T.additiveLineBundleFamily_calculus_rules S A).2.2.2.1 _ _ _ _ N M _ _ (inv (ptMap s (Ideal.Quotient.mk (Ideal.span {e}))))
      hN.isLB hM.isLB h
    rw [IsIso.inv_hom_id] at h'
    exact ⟨_, h'⟩
  · exact GlobalTheory.T.exists_lineBundleFamily_agreeing_smallExtension_tangent S A hA U M hM hI hT C e he hk h0 s N hN u' (hu ▸ h)

end GlobalTheory.DualOpen
