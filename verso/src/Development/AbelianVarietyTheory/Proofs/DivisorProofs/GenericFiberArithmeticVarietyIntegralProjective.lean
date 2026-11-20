import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalisationGenericSmoothCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZero
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

/- English proof (translation)
Introduce `k K _ _ _ _ X G _ p q j hp D h`. Take `⟨hG, hd, hη⟩` from `GenSmoothCover.genericFibre h hp`. Establish `hq : IsProjOver q` using `ProjSpace.isProjOver_of_isPullback_spMap _ hp h.isProjOver`. Establish `: IsProper q` using `CommonModel.isProper_of_isProjOver hq`. Use `h.isDomain` as an intermediate fact.

Use `IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)` as an intermediate fact. Establish `: IsPreimmersion j` using `MorphismProperty.of_isPullback hp.flip this`. Use `flat_specMap_localization (nonZeroDivisors k) K` as an intermediate fact. Establish `: Flat j` using `MorphismProperty.of_isPullback hp.flip this`. Establish `hs (x : G) : IsIso (j.stalkMap x)` using `GenSpread.isIso_stalkMap_of_flat j x`.

Use `⟨hG, LocallyOfFiniteType.isLocallyNoetherian q, hq, hd, hη, j.isEmbedding.injective, hs, fun x => ?_, fun z hz σ => ⟨fun y => hz ?_⟩⟩` and prove the remaining obligations. Use `hs x` as an intermediate fact. Establish `e` using `ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv`. Rewrite `e` using `[ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight]`. Conclude with `e` after adjusting the coercions.

Establish `hr : Set.range j = p ⁻¹' Set.range (spMap (algebraMap k K))`. Rewrite using `[← Scheme.Pullback.range_fst, ← hp.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Function.Surjective.range_comp hp.isoPullback.hom.surjective]`. Set `c : Sp ℂ` to `IsLocalRing.closedPoint ℂ`. Establish `hw : closι z (y.1 c) ∈ closure {z}`. Establish `: closι z (y.1 c) ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι` using `⟨_, rfl⟩`.

Rewrite `this` using `[Scheme.IdealSheafData.range_subschemeι]`. Simplify using `using this`. Establish `h₁ : p z ⤳ p (closι z (y.1 c))` using `(specializes_iff_mem_closure.2 hw).map p.continuous`. Establish `h₂ : p (closι z (y.1 c)) = spMap σ c`. Use `y.2` as an intermediate fact.

Rewrite using `[← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]`. Conclude with `congrArg (fun f : Sp ℂ ⟶ Sp k => f c) this`. Establish `h₃ : (spMap σ c).asIdeal = ⊥`. Express the relevant statement in the definitionally equal form `Ideal.comap σ (IsLocalRing.maximalIdeal ℂ) = ⊥`. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot]`.

Conclude with `Ideal.comap_bot_of_injective _ (ChernNull.injective_of_arithVar h σ)`. Rewrite `h₁` using `[h₂]`. Establish `h₄ : (p z).asIdeal ≤ (spMap σ c).asIdeal` using `(PrimeSpectrum.le_iff_specializes _ _).2 h₁`. Rewrite `h₄` using `[h₃, le_bot_iff]`. Rewrite using `[hr]`.

Use `⟨(⟨⊥, inferInstance⟩ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩` and prove the remaining obligations. Rewrite using `[h₄]`. Conclude with `Ideal.comap_bot_of_injective _ (IsFractionRing.injective k K)`.
-/
theorem genericFibre_facts : ∀ (k K : Type) [CommRing k] [Field K] [Algebra k K] [IsFractionRing k K] (X G : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap (algebraMap k K))) (D : ℕ), IsArithVar p D → ∃ (_ : IsIntegral G) (_ : IsLocallyNoetherian G), IsProjOver q ∧ topologicalKrullDim G = D ∧ j (genericPoint G) = genericPoint X ∧ Function.Injective j ∧ (∀ x, IsIso (j.stalkMap x)) ∧ (∀ x, Order.coheight (j x) = Order.coheight x) ∧ ∀ z : X, z ∉ Set.range j → ∀ σ : k →+* ℂ, IsEmpty (CxPts (closι z ≫ p) σ) := by
  intro k K _ _ _ _ X G _ p q j hp D h
  obtain ⟨hG, hd, hη⟩ := GenSmoothCover.genericFibre h hp
  have hq : IsProjOver q := ProjSpace.isProjOver_of_isPullback_spMap _ hp h.isProjOver
  have : IsProper q := CommonModel.isProper_of_isProjOver hq
  have := h.isDomain
  have := IsPreimmersion.of_isLocalization (R := k) (S := K) (nonZeroDivisors k)
  have : IsPreimmersion j := MorphismProperty.of_isPullback hp.flip this
  have := flat_specMap_localization (nonZeroDivisors k) K
  have : Flat j := MorphismProperty.of_isPullback hp.flip this
  have hs (x : G) : IsIso (j.stalkMap x) := GenSpread.isIso_stalkMap_of_flat j x
  refine ⟨hG, LocallyOfFiniteType.isLocallyNoetherian q, hq, hd, hη, j.isEmbedding.injective, hs,
    fun x => ?_, fun z hz σ => ⟨fun y => hz ?_⟩⟩
  · have := hs x
    have e := ringKrullDim_eq_of_ringEquiv (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at e
    exact_mod_cast e
  · have hr : Set.range j = p ⁻¹' Set.range (spMap (algebraMap k K)) := by
      rw [← Scheme.Pullback.range_fst, ← hp.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
        Function.Surjective.range_comp hp.isoPullback.hom.surjective]
    let c : Sp ℂ := IsLocalRing.closedPoint ℂ
    have hw : closι z (y.1 c) ∈ closure {z} := by
      have : closι z (y.1 c) ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z})).subschemeι :=
        ⟨_, rfl⟩
      rw [Scheme.IdealSheafData.range_subschemeι] at this
      simpa using this
    have h₁ : p z ⤳ p (closι z (y.1 c)) := (specializes_iff_mem_closure.2 hw).map p.continuous
    have h₂ : p (closι z (y.1 c)) = spMap σ c := by
      have := y.2
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun f : Sp ℂ ⟶ Sp k => f c) this
    have h₃ : (spMap σ c).asIdeal = ⊥ := by
      change Ideal.comap σ (IsLocalRing.maximalIdeal ℂ) = ⊥
      rw [IsLocalRing.maximalIdeal_eq_bot]
      exact Ideal.comap_bot_of_injective _ (ChernNull.injective_of_arithVar h σ)
    rw [h₂] at h₁
    have h₄ : (p z).asIdeal ≤ (spMap σ c).asIdeal := (PrimeSpectrum.le_iff_specializes _ _).2 h₁
    rw [h₃, le_bot_iff] at h₄
    rw [hr]
    refine ⟨(⟨⊥, inferInstance⟩ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [h₄]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective k K)

end GlobalTheory.Mix
