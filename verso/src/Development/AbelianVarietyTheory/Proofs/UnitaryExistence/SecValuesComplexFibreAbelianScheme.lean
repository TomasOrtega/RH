import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfS
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

/- English proof (translation)
Introduce `hT E _ _ _ H Dw l Xo y s`. Establish `hsm : Smooth (gxSnd y)`. Use `Xo.univ.t.semi.smooth` as an intermediate fact. Conclude with `inferInstanceAs (Smooth (pullback.fst y Xo.univ.t.G.hom))`. Establish `hred : IsReduced (Gx y)` using `(isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ _ (gxSnd y) hsm).1`.

Establish `h1 : ∀ (a : ℂ) i (f : Γ(Gx y, (PPx y).U i)) (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (scal y a i * f) = a * valAt' pt ((PPx y).U i) f` using `fun a i f pt hp => by`. Distinguish the cases in `h : ⊤ ≤ pt ⁻¹ᵁ (PPx y).U i`. Rewrite using `[valAt'_mul]`. Conclude with `congrArg (· * _) (valAt'_constFn pt (gxSnd y) hp _ a h)`. Rewrite using `[valAt'_of_not_le pt h, valAt'_of_not_le pt h, mul_zero]`.

Establish `h3 : ∀ i (f g : Γ(Gx y, (PPx y).U i)), (∀ pt : Sp ℂ ⟶ Gx y, pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) f = valAt' pt ((PPx y).U i) g) → f = g` using `fun i f g h => ComplexPoints.eq_of_valAt'_eq (gxSnd y) _ f g fun pt hp _ => h pt hp`. Use `⟨fun a i pt hp => h1 a i _ pt hp, ⟨fun hs => ?_, ?_⟩, fun s' h i => h3 i _ _ (h i)⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `h0 : ∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s.f i) = 0` using `fun i pt hp => by`. Assume the negation of the conclusion as `h`.

Conclude with `hne ⟨i, pt, hp, h⟩`. Establish `hall : ∀ (a : ℂ) i, s.f i = scal y a i * s.f i` using `fun a i => h3 i _ _ fun pt hp => by`. Rewrite using `[h1 a i _ pt hp, h0 i pt hp, mul_zero]`. Conclude with `zero_ne_one ((hs s).unique (hall 0) (hall 1))`. Introduce and unpack `⟨j, q, hq, hv⟩ s'`.

Take `⟨s₀, hs₀⟩` from `gfp_gen hT y`. Take `⟨c, hc, -⟩` from `hs₀ s`. Establish `hc0 : c ≠ 0` using `fun h => hv (by rw [hc j, h1 c j _ q hq, h, zero_mul])`. Take `⟨b, hb, hu⟩` from `hs₀ s'`. Use `⟨b / c, fun i => h3 i _ _ fun pt hp => ?_, fun a ha => ?_⟩` and prove the remaining obligations.

Rewrite using `[h1 _ i _ pt hp, hb i, hc i, h1 _ i _ pt hp, h1 _ i _ pt hp, ← mul_assoc, div_mul_cancel₀ _ hc0]`. Rewrite using `[eq_div_iff hc0]`. Use `hu _ fun i => h3 i _ _ fun pt hp => ?_` and prove the remaining obligations. Rewrite using `[h1 _ i _ pt hp, ha i, hc i, h1 _ i _ pt hp, h1 _ i _ pt hp, mul_assoc]`.
-/
theorem sec_values_complex_fibre : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (y : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx y)), (∀ (a : ℂ) i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (scal y a i * s.f i) = a * valAt' pt ((PPx y).U i) (s.f i)) ∧ (SecGen y s ↔ ∃ (i : (PPx y).ι) (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ ∧ valAt' pt ((PPx y).U i) (s.f i) ≠ 0) ∧ ∀ s' : LB.Sec (PPx y), (∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s'.f i) = valAt' pt ((PPx y).U i) (s.f i)) → ∀ i, s'.f i = s.f i := by
  intro hT E _ _ _ H Dw l Xo y s
  have hsm : Smooth (gxSnd y) := by
    have := Xo.univ.t.semi.smooth
    exact inferInstanceAs (Smooth (pullback.fst y Xo.univ.t.G.hom))
  have hred : IsReduced (Gx y) :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ _ (gxSnd y) hsm).1
  have h1 : ∀ (a : ℂ) i (f : Γ(Gx y, (PPx y).U i)) (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ →
      valAt' pt ((PPx y).U i) (scal y a i * f) = a * valAt' pt ((PPx y).U i) f := fun a i f pt hp => by
    by_cases h : ⊤ ≤ pt ⁻¹ᵁ (PPx y).U i
    · rw [valAt'_mul]
      exact congrArg (· * _) (valAt'_constFn pt (gxSnd y) hp _ a h)
    · rw [valAt'_of_not_le pt h, valAt'_of_not_le pt h, mul_zero]
  have h3 : ∀ i (f g : Γ(Gx y, (PPx y).U i)), (∀ pt : Sp ℂ ⟶ Gx y, pt ≫ gxSnd y = 𝟙 _ →
      valAt' pt ((PPx y).U i) f = valAt' pt ((PPx y).U i) g) → f = g := fun i f g h =>
    ComplexPoints.eq_of_valAt'_eq (gxSnd y) _ f g fun pt hp _ => h pt hp
  refine ⟨fun a i pt hp => h1 a i _ pt hp, ⟨fun hs => ?_, ?_⟩, fun s' h i => h3 i _ _ (h i)⟩
  · by_contra hne
    have h0 : ∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s.f i) = 0 := fun i pt hp => by
      by_contra h
      exact hne ⟨i, pt, hp, h⟩
    have hall : ∀ (a : ℂ) i, s.f i = scal y a i * s.f i := fun a i => h3 i _ _ fun pt hp => by
      rw [h1 a i _ pt hp, h0 i pt hp, mul_zero]
    exact zero_ne_one ((hs s).unique (hall 0) (hall 1))
  · rintro ⟨j, q, hq, hv⟩ s'
    obtain ⟨s₀, hs₀⟩ := gfp_gen hT y
    obtain ⟨c, hc, -⟩ := hs₀ s
    have hc0 : c ≠ 0 := fun h => hv (by rw [hc j, h1 c j _ q hq, h, zero_mul])
    obtain ⟨b, hb, hu⟩ := hs₀ s'
    refine ⟨b / c, fun i => h3 i _ _ fun pt hp => ?_, fun a ha => ?_⟩
    · rw [h1 _ i _ pt hp, hb i, hc i, h1 _ i _ pt hp, h1 _ i _ pt hp, ← mul_assoc, div_mul_cancel₀ _ hc0]
    · rw [eq_div_iff hc0]
      refine hu _ fun i => h3 i _ _ fun pt hp => ?_
      rw [h1 _ i _ pt hp, ha i, hc i, h1 _ i _ pt hp, h1 _ i _ pt hp, mul_assoc]

end GlobalTheory
