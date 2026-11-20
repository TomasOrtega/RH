import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.FieldExtensionBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionTrivialCases
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.BlowupDataOfSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SmoothBaseChangeCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxOrderReduction

/- English proof (translation)
Introduce `T hT L _ _ f B b pB hpB IB EB hTB Q a b' hpb A y`. Substitute `hpB` using the available equality. Establish `hQ : IsPullback (Limits.pullback.fst b (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))) (Limits.pullback.snd b (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))) b (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))` using `IsPullback.of_hasPullback _ _`. Set `E : Q ≅ Limits.pullback (b ≫ T.structMap) (specMapOfFieldHom T.base L f)` to `hpb.isoIsPullback B (Limits.pullback T.structMap (specMapOfFieldHom T.base L f)) hQ ≪≫ Limits.pullbackRightPullbackFstIso T.structMap (specMapOfFieldHom T.base L f) b`. Establish `he : E.hom ≫ Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f) = a`.

Simplify using `[E, Iso.trans_hom]`. Establish `hcomp : A.comap a = (A.comap (Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f))).comap E.hom`. Rewrite using `[← he]`. Simplify using `[Scheme.IdealSheafData.comap_comp]`. Establish `h1 : orderAt (A.comap a) y = orderAt (A.comap (Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f))) (E.hom.base y)`.

Rewrite using `[hcomp]`. Conclude with `FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isIso E.hom _ y`. Establish `h2` using `hG.orderAt_baseChange (MarkedIdealWithBoundary.mk T.base B (b ≫ T.structMap) IB T.mult EB) hTB L f A (E.hom.base y)`. Establish `h3 : orderAt A ((Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f)).base (E.hom.base y)) = orderAt A (a y)`. Rewrite using `[← he]`.

Simplify using the standard rewrite rules. Conclude with `h1.trans (h2.trans h3)`.
-/
private theorem orderAtBaseFieldChangeInvariance_of_geometryHypotheses (hG : PrincipalizationGeometryHypotheses.{u}) :
    OrderAtBaseFieldChangeInvariance.{u} := by
  intro T hT L _ _ f B b pB hpB IB EB hTB Q a b' hpb A y
  subst hpB
  have hQ : IsPullback
      (Limits.pullback.fst b (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f)))
      (Limits.pullback.snd b (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f))) b
      (Limits.pullback.fst T.structMap (specMapOfFieldHom T.base L f)) :=
    IsPullback.of_hasPullback _ _
  let E : Q ≅ Limits.pullback (b ≫ T.structMap) (specMapOfFieldHom T.base L f) :=
    hpb.isoIsPullback B (Limits.pullback T.structMap (specMapOfFieldHom T.base L f)) hQ ≪≫
      Limits.pullbackRightPullbackFstIso T.structMap (specMapOfFieldHom T.base L f) b
  have he : E.hom ≫ Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f) = a := by
    simp [E, Iso.trans_hom]
  have hcomp : A.comap a =
      (A.comap
        (Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f))).comap E.hom := by
    rw [← he]
    simp [Scheme.IdealSheafData.comap_comp]
  have h1 : orderAt (A.comap a) y
      = orderAt (A.comap (Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f)))
          (E.hom.base y) := by
    rw [hcomp]
    exact FunctorialResolution.EmbeddedResolution.orderAt_comap_of_isIso E.hom _ y
  have h2 := hG.orderAt_baseChange
    (MarkedIdealWithBoundary.mk T.base B (b ≫ T.structMap) IB T.mult EB) hTB L f A (E.hom.base y)
  have h3 : orderAt A
      ((Limits.pullback.fst (b ≫ T.structMap) (specMapOfFieldHom T.base L f)).base (E.hom.base y))
      = orderAt A (a y) := by
    rw [← he]
    simp
  exact h1.trans (h2.trans h3)

/- English proof (translation)
Establish `h` using `isLocallyMonomialPrincipalization_monomialPrincipalization hG.monomialInputs hinv (orderAtBaseFieldChangeInvariance_of_geometryHypotheses hG) (fun _ => True)`. Conclude with `{ cert := fun T hTm i hi => h.cert T hTm trivial i hi center_nonempty := fun T hTm i hi => h.center_nonempty T hTm trivial i hi resolves := fun T hTm => h.resolves T hTm trivial trivial_of_coSupport_empty := fun T hTm hc => h.trivial_of_coSupport_empty T hTm trivial hc }`.
-/
theorem monomialPrincipalization_spec (hG : PrincipalizationGeometryHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) : MonomialPrincipalizationHypotheses hinv := by
  have h := isLocallyMonomialPrincipalization_monomialPrincipalization hG.monomialInputs hinv
      (orderAtBaseFieldChangeInvariance_of_geometryHypotheses hG) (fun _ => True)
  exact
    { cert := fun T hTm i hi => h.cert T hTm trivial i hi
      center_nonempty := fun T hTm i hi => h.center_nonempty T hTm trivial i hi
      resolves := fun T hTm => h.resolves T hTm trivial
      trivial_of_coSupport_empty := fun T hTm hc => h.trivial_of_coSupport_empty T hTm trivial hc }

/- English proof (translation)
Establish `hmon : MonomialPrincipalizationHypotheses hinv` using `monomialPrincipalization_spec hG hinv`. Use `{ cert := fun T hT hdim i hi => certificate_orderReductionSeq hG hinv hmon hspec hT hdim i hi orderRed_equiv := fun T hT hdim hE hord => orderReductionSeq_isomorphic_of_boundary_nil hG hinv hmon hspec hT hdim hE hord center_nonempty := fun T hT hdim i hi => center_support_nonempt …` and prove the remaining obligations. Introduce `T hT hdim L _ _ f E' hE hT' hdim'`. Conclude with `orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim L (baseChangeStructMap T L f) (baseChangeProj T L f) E' hE.symm hT' hdim' (baseChangeCompatible_baseChangeProj_of_isOrderReduction hG hinv n A B hspec T hT hdim L f)`. Introduce `T hT hdim L _ _ f E' hE hT' hdim'`.

Establish `hp` using `orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim L (baseChangeStructMap T L f) (baseChangeProj T L f) E' hE.symm hT' hdim' (baseChangeCompatible_baseChangeProj_of_isOrderReduction hG hinv n A B hspec T hT hdim L f)`. Establish `hsurj : AlgebraicGeometry.Surjective (baseChangeProj T L f)` using `instSurjectivePullbackFstSpecMapField T.base L f T.scheme T.structMap`. Conclude with `hp.isStrictPullback_of_surjective fun i hi => (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp (center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi)`. Introduce `T hT hdim Y q h hsm hq E' hE hT' hdim'`. Use `hsm` as an intermediate fact.

Conclude with `orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim T.base q h E' hE.symm hT' hdim' (baseChangeCompatible_of_smooth hG hinv n A B hspec T hT hdim h q hq)`. Introduce `T hT hdim Y q h hsm hsurj hq E' hE hT' hdim'`. Use `hsm` as an intermediate fact. Use `hsurj` as an intermediate fact. Establish `hp` using `orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim T.base q h E' hE.symm hT' hdim' (baseChangeCompatible_of_smooth hG hinv n A B hspec T hT hdim h q hq)`.

Conclude with `hp.isStrictPullback_of_surjective fun i hi => (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp (center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi)`.
-/
theorem isMaxOrderReduction_orderReductionSeq (hG : PrincipalizationGeometryHypotheses.{u}) (hinv : ComapIsoInvariance.{u}) (n : ℕ)
    (A B : PrincipalizationAssignment.{u}) (hspec : IsOrderReduction (fun d => d ≤ n) A B) :
    IsMaxOrderReduction (fun d => d ≤ n) (fun T => orderReductionSeq hinv T (principalizationOfDimLe T A)) A := by
  have hmon : MonomialPrincipalizationHypotheses hinv := monomialPrincipalization_spec hG hinv
  refine
    { cert := fun T hT hdim i hi => certificate_orderReductionSeq hG hinv hmon hspec hT hdim i hi
      orderRed_equiv := fun T hT hdim hE hord =>
        orderReductionSeq_isomorphic_of_boundary_nil hG hinv hmon hspec hT hdim hE hord
      center_nonempty := fun T hT hdim i hi =>
        center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi
      resolves := fun T hT hdim => isResolution_orderReductionSeq hG hinv hmon hspec hT hdim
      trivial_of_coSupport_empty := fun T hT hdim hc =>
        orderReductionSeq_length_eq_zero_of_orderAtLeastLocus_empty hinv T A hc
      base_change := ?_
      base_change_strict := ?_
      smooth_pullback := ?_
      smooth_pullback_strict := ?_ }
  · intro T hT hdim L _ _ f E' hE hT' hdim'
    exact orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim L
      (baseChangeStructMap T L f) (baseChangeProj T L f) E' hE.symm hT' hdim'
      (baseChangeCompatible_baseChangeProj_of_isOrderReduction hG hinv n A B hspec T hT hdim L f)
  · intro T hT hdim L _ _ f E' hE hT' hdim'
    have hp := orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim L
      (baseChangeStructMap T L f) (baseChangeProj T L f) E' hE.symm hT' hdim'
      (baseChangeCompatible_baseChangeProj_of_isOrderReduction hG hinv n A B hspec T hT hdim L f)
    have hsurj : AlgebraicGeometry.Surjective (baseChangeProj T L f) :=
      instSurjectivePullbackFstSpecMapField T.base L f T.scheme T.structMap
    exact hp.isStrictPullback_of_surjective fun i hi =>
      (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
        (center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi)
  · intro T hT hdim Y q h hsm hq E' hE hT' hdim'
    have := hsm
    exact orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim T.base q h E'
      hE.symm hT' hdim' (baseChangeCompatible_of_smooth hG hinv n A B hspec T hT hdim h q hq)
  · intro T hT hdim Y q h hsm hsurj hq E' hE hT' hdim'
    have := hsm
    have := hsurj
    have hp := orderReductionSeq_isPullbackBlowupSequence_pullbackOverField hG hinv n A B hspec T hT hdim T.base q h E'
      hE.symm hT' hdim' (baseChangeCompatible_of_smooth hG hinv n A B hspec T hT hdim h q hq)
    exact hp.isStrictPullback_of_surjective fun i hi =>
      (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp
        (center_support_nonempty_orderReductionSeq hG hinv hmon hspec hT hdim i hi)

/- English proof (translation)
The claim follows from `isMaxOrderReduction_orderReductionSeq hG comapIsoInvariance n A B hspec`.
-/
theorem isMaxOrderReduction_canonicalAlgorithmRules (hG : PrincipalizationGeometryHypotheses.{u})
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) (n : ℕ) (A B : PrincipalizationAssignment.{u})
    (hspec : IsOrderReduction (fun d => d ≤ n) A B) :
    IsMaxOrderReduction (fun d => d ≤ n) ((canonicalAlgorithmRules hres).maxOrderFamily A) A :=
  isMaxOrderReduction_orderReductionSeq hG comapIsoInvariance n A B hspec

end MaxOrderReduction

end FunctorialResolution.EmbeddedResolution

end
