import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfOpenImmersionIntegralSche
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionFieldEquivOpenImmersionSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeLocalizationSameFractionFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocModelProj

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw in

/- English proof (translation)
Establish `: LocallyOfFiniteType (spMap (algebraMap ℂ S))` using `HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)`. Take `⟨N, i, _, _, e⟩` from `(isAmpleLB_of_isAffine (LB.isLB_triv (Sp S))).isQProjOver (spMap (algebraMap ℂ S))`. Use `isProper_str ℂ N` as an intermediate fact. Conclude with `⟨i.image, isIntegral_image i, i.imageι ≫ PSpace.str ℂ N, i.toImage, ⟨N, i.imageι, inferInstance, rfl⟩, inferInstance, inferInstance, by rw [i.toImage_imageι_assoc, e]⟩`.
-/
theorem exists_projective_openImmersion (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] :
    ∃ (Y : Scheme.{0}) (_ : IsIntegral Y) (p : Y ⟶ Sp ℂ) (j : Sp S ⟶ Y),
      IsProjOver p ∧ IsOpenImmersion j ∧ LocallyOfFiniteType p ∧ j ≫ p = spMap (algebraMap ℂ S) := by
  have : LocallyOfFiniteType (spMap (algebraMap ℂ S)) :=
    HasRingHomProperty.Spec_iff.2 (RingHom.finiteType_algebraMap.2 inferInstance)
  obtain ⟨N, i, _, _, e⟩ := (isAmpleLB_of_isAffine (LB.isLB_triv (Sp S))).isQProjOver (spMap (algebraMap ℂ S))
  have := isProper_str ℂ N
  exact ⟨i.image, isIntegral_image i, i.imageι ≫ PSpace.str ℂ N, i.toImage, ⟨N, i.imageι, inferInstance, rfl⟩,
    inferInstance, inferInstance, by rw [i.toImage_imageι_assoc, e]⟩

/- English proof (translation)
Establish `: Nonempty (Sp S)` using `inferInstance`. Rewrite using `[← GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion ℂ Y (Sp S) p j]`. Express the relevant statement in the definitionally equal form `topologicalKrullDim (PrimeSpectrum S) = _`. Rewrite using `[PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, GlobalTheory.ringKrullDim_eq_of_trdeg_eq ℂ S h]`.
-/
theorem topologicalKrullDim_eq_of_openImmersion (S : Type) [CommRing S] [IsDomain S] [Algebra ℂ S] [Algebra.FiniteType ℂ S] (Y : Scheme.{0}) [IsIntegral Y]
    (p : Y ⟶ Sp ℂ) [LocallyOfFiniteType p] (j : Sp S ⟶ Y) [IsOpenImmersion j] (n : ℕ) (h : Algebra.trdeg ℂ S = n) :
    topologicalKrullDim Y = n := by
  have : Nonempty (Sp S) := inferInstance
  rw [← GlobalTheory.OpenImmDim.topologicalKrullDim_eq_of_isOpenImmersion ℂ Y (Sp S) p j]
  change topologicalKrullDim (PrimeSpectrum S) = _
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, GlobalTheory.ringKrullDim_eq_of_trdeg_eq ℂ S h]

/- English proof (translation)
Introduce `L _ c R n x hR hx`. Take `⟨S, hS, q, hq, hft, hfrac, hmem⟩` from `GlobalTheory.T.exists_finiteType_localization_same_fractionField L c R hR`. Use `letI : Algebra ℂ S := (c.codRestrict S hS).toAlgebra`. Use `letI : Algebra S L := S.subtype.toAlgebra`. Use `letI : Algebra ℂ L := c.toAlgebra`.

Use `haveI : IsScalarTower ℂ S L := IsScalarTower.of_algebraMap_eq' rfl`. Use `haveI : Algebra.FiniteType ℂ S := hft`. Use `haveI : FaithfulSMul S L := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective`. Use `haveI : IsFractionRing S L := by`. Use `IsFractionRing.of_field S L fun f => ?_` and prove the remaining obligations.

Take `⟨a, ha, b, hb, hb0, e⟩` from `hfrac f`. Use `⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f = a / b`. Rewrite using `[← e, mul_div_cancel_right₀ _ hb0]`. Establish `htr : Algebra.trdeg ℂ S = n`.

Establish `h2` using `IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx`. Establish `: Algebra.IsAlgebraic S L` using `IsLocalization.isAlgebraic L (nonZeroDivisors S)`. Rewrite `h2` using `[← trdeg_add_eq ℂ S (A := L), trdeg_eq_zero (R := S) (A := L), add_zero]`. Rewrite using `[← h2, Cardinal.mk_fin]`. Take `⟨Y, hY, p, j, hproj, hj, hlft, hjp⟩` from `exists_projective_openImmersion S`.

Take `⟨e, hc, hloc⟩` from `GlobalTheory.T.exists_functionFieldEquiv_openImmersionSpec S Y p j hjp`. Set `e2 : FractionRing S ≃ₐ[S] L` to `IsLocalization.algEquiv (nonZeroDivisors S) (FractionRing S) L`. Use `⟨Y, hY, p, e.trans e2.toRingEquiv, j.base ⟨q, hq⟩, hproj, topologicalKrullDim_eq_of_openImmersion S Y p j n htr, fun a => ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e2 (e (GlobalTheory.Cartier.constFn p a)) = c a`. Rewrite using `[hc, IsScalarTower.algebraMap_apply ℂ S (FractionRing S), AlgEquiv.commutes]`.

Both sides reduce to the same expression. Use extensionality with `g`. Establish `h1 : g ∈ (locRing (j.base ⟨q, hq⟩)).map (e.trans e2.toRingEquiv).toRingHom ↔ e2.symm g ∈ (locRing (j.base ⟨q, hq⟩)).map e.toRingHom`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`.

Conclude with `⟨u, hu, by simp⟩`. Introduce and unpack `⟨u, hu, hu'⟩`. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `e2 (e u) = g`. Rewrite using `[show e u = e2.symm g from hu', AlgEquiv.apply_symm_apply]`.

Rewrite using `[h1, hloc ⟨q, hq⟩, hmem g]`. Use `exists₂_congr fun a b => and_congr_right fun _ => ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `congrArg e2 h` as an intermediate fact.

Rewrite `this` using `[map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]`. Then use the resulting hypothesis. Introduce `h`. Apply `e2.injective` to reduce the goal to its premises. Rewrite using `[map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]`. Conclude with `h`.
-/
theorem exists_projective_of_isLocModel : ∀ (L : Type) [Field L] (c : ℂ →+* L) (R : Subring L) (n : ℕ) (x : Fin n → L), IsLocModel c R → TrBasis c x →
  ∃ (Y : AlgebraicGeometry.Scheme.{0}) (_ : AlgebraicGeometry.IsIntegral Y) (p : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) (e : Y.functionField ≃+* L) (y : Y),
    IsProjOver p ∧ topologicalKrullDim Y = n ∧ (∀ a, e (GlobalTheory.Cartier.constFn p a) = c a) ∧ (locRing y).map e.toRingHom = R := by
  intro L _ c R n x hR hx
  obtain ⟨S, hS, q, hq, hft, hfrac, hmem⟩ := GlobalTheory.T.exists_finiteType_localization_same_fractionField L c R hR
  letI : Algebra ℂ S := (c.codRestrict S hS).toAlgebra
  letI : Algebra S L := S.subtype.toAlgebra
  letI : Algebra ℂ L := c.toAlgebra
  haveI : IsScalarTower ℂ S L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Algebra.FiniteType ℂ S := hft
  haveI : FaithfulSMul S L := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI : IsFractionRing S L := by
    refine IsFractionRing.of_field S L fun f => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hfrac f
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change f = a / b
    rw [← e, mul_div_cancel_right₀ _ hb0]
  have htr : Algebra.trdeg ℂ S = n := by
    have h2 := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hx
    have : Algebra.IsAlgebraic S L := IsLocalization.isAlgebraic L (nonZeroDivisors S)
    rw [← trdeg_add_eq ℂ S (A := L), trdeg_eq_zero (R := S) (A := L), add_zero] at h2
    rw [← h2, Cardinal.mk_fin]
  obtain ⟨Y, hY, p, j, hproj, hj, hlft, hjp⟩ := exists_projective_openImmersion S
  obtain ⟨e, hc, hloc⟩ := GlobalTheory.T.exists_functionFieldEquiv_openImmersionSpec S Y p j hjp
  let e2 : FractionRing S ≃ₐ[S] L := IsLocalization.algEquiv (nonZeroDivisors S) (FractionRing S) L
  refine ⟨Y, hY, p, e.trans e2.toRingEquiv, j.base ⟨q, hq⟩, hproj, topologicalKrullDim_eq_of_openImmersion S Y p j n htr, fun a => ?_, ?_⟩
  · change e2 (e (GlobalTheory.Cartier.constFn p a)) = c a
    rw [hc, IsScalarTower.algebraMap_apply ℂ S (FractionRing S), AlgEquiv.commutes]
    rfl
  · ext g
    have h1 : g ∈ (locRing (j.base ⟨q, hq⟩)).map (e.trans e2.toRingEquiv).toRingHom ↔
        e2.symm g ∈ (locRing (j.base ⟨q, hq⟩)).map e.toRingHom := by
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, by simp⟩
      · rintro ⟨u, hu, hu'⟩
        refine ⟨u, hu, ?_⟩
        change e2 (e u) = g
        rw [show e u = e2.symm g from hu', AlgEquiv.apply_symm_apply]
    rw [h1, hloc ⟨q, hq⟩, hmem g]
    refine exists₂_congr fun a b => and_congr_right fun _ => ?_
    constructor
    · intro h
      have := congrArg e2 h
      rwa [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes] at this
    · intro h
      apply e2.injective
      rw [map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes, AlgEquiv.commutes]
      exact h

end GlobalTheory.LocModelProj
