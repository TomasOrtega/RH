import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsUFD
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.WeierstrassPolynomialRing
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermGeneralCoordinates
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermWeierstrassDivision
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGermWeierstrassPreparation
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PWeierstrassPolynomialDivision
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParametricCircleIntegralAnalytic
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCircleArgumentPrinciple
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPowerSumsEsymmAnalytic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Polynomial

noncomputable section

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_mkGerm {τ : Type} [Fintype τ] (f : (τ → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    ((mkGerm f hf : holGerms (0 : τ → ℂ)) : Germ (𝓝 (0 : τ → ℂ)) ℂ) = ↑f := rfl

/- English proof (translation)
Use `IsUnit.of_mul_eq_one (mkGerm (fun x => (e x)⁻¹) (he.inv he0)) (Subtype.ext ?_)` and prove the remaining obligations. Use `show ((fun x => e x * (e x)⁻¹ : (τ → ℂ) → ℂ) : Germ (𝓝 (0 : τ → ℂ)) ℂ) = ((fun _ => (1 : ℂ) : (τ → ℂ) → ℂ) : Germ (𝓝 (0 : τ → ℂ)) ℂ)`. Conclude with `Germ.coe_eq.2 (by filter_upwards [he.continuousAt.eventually_ne he0] with x hx`. Conclude with `mul_inv_cancel₀ hx)`.
-/
theorem isUnit_mkGerm {τ : Type} [Fintype τ] (e : (τ → ℂ) → ℂ) (he : AnalyticAt ℂ e 0) (he0 : e 0 ≠ 0) :
    IsUnit (mkGerm e he) := by
  refine IsUnit.of_mul_eq_one (mkGerm (fun x => (e x)⁻¹) (he.inv he0)) (Subtype.ext ?_)
  show ((fun x => e x * (e x)⁻¹ : (τ → ℂ) → ℂ) : Germ (𝓝 (0 : τ → ℂ)) ℂ) =
    ((fun _ => (1 : ℂ) : (τ → ℂ) → ℂ) : Germ (𝓝 (0 : τ → ℂ)) ℂ)
  exact Germ.coe_eq.2 (by
    filter_upwards [he.continuousAt.eventually_ne he0] with x hx
    exact mul_inv_cancel₀ hx)

/- English proof (translation)
Use `hN (Option σ) 0` as an intermediate fact. Use `hR` as an intermediate fact. Use `{ irreducible_iff_prime := fun {φ} => ⟨fun hφ => ?_, Prime.irreducible⟩ }` and prove the remaining obligations. Take `⟨f, hf, hfφ⟩` from `φ.2`. Establish `hnz : ¬ ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0` using `fun h => hφ.ne_zero (Subtype.ext (by rw [← hfφ]; exact Germ.coe_eq.2 h))`.

Take `⟨A, d, hAd⟩` from `hG σ f hf hnz`. Establish `hfA : AnalyticAt ℂ (f ∘ A) 0` using `hf.comp_of_eq (A.analyticAt 0) (map_zero A)`. Establish `hT : germAffineEquiv A (0 : Option σ → ℂ) φ = mkGerm (f ∘ A) hfA`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show ((germPull (fun z : Option σ → ℂ => A z + 0) ((A.analyticAt 0).add analyticAt_const) (by simp) φ : holGerms (0 : Option σ → ℂ)) : Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = ↑(f ∘ A)`.

Rewrite using `[germPull_coe _ _ _ φ f hfφ]`. Use `congr 1`. Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules. Use `(MulEquiv.prime_iff (germAffineEquiv A (0 : Option σ → ℂ))).1 ?_` and prove the remaining obligations.

Rewrite using `[hT]`. Establish `hirrA : Irreducible (mkGerm (f ∘ A) hfA)`. Rewrite using `[← hT]`. Conclude with `(MulEquiv.irreducible_iff (germAffineEquiv A (0 : Option σ → ℂ))).2 hφ`. Take `⟨e, c, he, he0, hc, hc0, hfe⟩` from `hP σ d (f ∘ A) hfA hAd`.

Establish `hE` using `isUnit_mkGerm e he he0`. Establish `hF : mkGerm (f ∘ A) hfA = polyToGerm σ (weierstrassPoly c hc) * mkGerm e he`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Subring.coe_mul, polyToGerm_weierstrassPoly, coe_mkGerm, coe_mkGerm, ← Germ.coe_mul]`. Conclude with `Germ.coe_eq.2 (by filter_upwards [hfe] with x hx`.

Rewrite using `[hx, Pi.mul_apply, mul_comm])`. Establish `hassoc : Associated (polyToGerm σ (weierstrassPoly c hc)) (mkGerm (f ∘ A) hfA)` using `⟨hE.unit, by rw [hF, IsUnit.unit_spec]⟩`. Establish `hirrW : Irreducible (polyToGerm σ (weierstrassPoly c hc))` using `hassoc.irreducible_iff.2 hirrA`. Use `hassoc.prime_iff.1 ?_` and prove the remaining obligations. Establish `hprimeω : Prime (weierstrassPoly c hc)` using `UniqueFactorizationMonoid.irreducible_iff_prime.1 (weierstrassPoly_irreducible c hc hc0 hirrW)`.

Use `prime_map_of_prime (polyToGerm σ) hprimeω hirrW.ne_zero ?_ (weierstrassPoly_dvd_of_polyToGerm_dvd c hc hc0)` and prove the remaining obligations. Introduce `g`. Take `⟨g₀, hg₀, hg₀g⟩` from `g.2`. Take `⟨q, a, hq, ha, hdiv⟩` from `hD σ d (f ∘ A) g₀ hfA hg₀ hAd`. Use `⟨mkGerm (q * e) (hq.mul he), finPoly fun j => mkGerm (a j) (ha j), Subtype.ext ?_⟩` and prove the remaining obligations.

Rewrite using `[Subring.coe_add, Subring.coe_mul, polyToGerm_weierstrassPoly, polyToGerm_finPoly, coe_mkGerm, ← hg₀g, ← Germ.coe_mul, ← Germ.coe_add]`. Conclude with `Germ.coe_eq.2 (by filter_upwards [hdiv, hfe] with x hx hx'`. Simplify using `only [Pi.add_apply, Pi.mul_apply]`. Rewrite using `[hx, hx']`. Use the proof step `ring)`.
-/
theorem uniqueFactorizationMonoid_holGerms_option (hN : AnalyticGermsNoetherian.Statement)
    (hG : GeneralLinearCoordinates.Statement) (hP : WeierstrassPreparation.Statement)
    (hD : WeierstrassDivision.Statement) (σ : Type) [Fintype σ]
    (hR : UniqueFactorizationMonoid (holGerms (0 : σ → ℂ))) :
    UniqueFactorizationMonoid (holGerms (0 : Option σ → ℂ)) := by
  have := hN (Option σ) 0
  have := hR
  refine { irreducible_iff_prime := fun {φ} => ⟨fun hφ => ?_, Prime.irreducible⟩ }
  obtain ⟨f, hf, hfφ⟩ := φ.2
  have hnz : ¬ ∀ᶠ x in 𝓝 (0 : Option σ → ℂ), f x = 0 := fun h =>
    hφ.ne_zero (Subtype.ext (by rw [← hfφ]; exact Germ.coe_eq.2 h))
  obtain ⟨A, d, hAd⟩ := hG σ f hf hnz
  have hfA : AnalyticAt ℂ (f ∘ A) 0 := hf.comp_of_eq (A.analyticAt 0) (map_zero A)

  have hT : germAffineEquiv A (0 : Option σ → ℂ) φ = mkGerm (f ∘ A) hfA := by
    apply Subtype.ext
    show ((germPull (fun z : Option σ → ℂ => A z + 0) ((A.analyticAt 0).add analyticAt_const) (by simp) φ : holGerms (0 : Option σ → ℂ)) :
      Germ (𝓝 (0 : Option σ → ℂ)) ℂ) = ↑(f ∘ A)
    rw [germPull_coe _ _ _ φ f hfφ]
    congr 1
    funext z
    simp
  refine (MulEquiv.prime_iff (germAffineEquiv A (0 : Option σ → ℂ))).1 ?_
  rw [hT]
  have hirrA : Irreducible (mkGerm (f ∘ A) hfA) := by
    rw [← hT]; exact (MulEquiv.irreducible_iff (germAffineEquiv A (0 : Option σ → ℂ))).2 hφ

  obtain ⟨e, c, he, he0, hc, hc0, hfe⟩ := hP σ d (f ∘ A) hfA hAd
  have hE := isUnit_mkGerm e he he0
  have hF : mkGerm (f ∘ A) hfA = polyToGerm σ (weierstrassPoly c hc) * mkGerm e he := by
    apply Subtype.ext
    rw [Subring.coe_mul, polyToGerm_weierstrassPoly, coe_mkGerm, coe_mkGerm, ← Germ.coe_mul]
    exact Germ.coe_eq.2 (by
      filter_upwards [hfe] with x hx
      rw [hx, Pi.mul_apply, mul_comm])
  have hassoc : Associated (polyToGerm σ (weierstrassPoly c hc)) (mkGerm (f ∘ A) hfA) :=
    ⟨hE.unit, by rw [hF, IsUnit.unit_spec]⟩
  have hirrW : Irreducible (polyToGerm σ (weierstrassPoly c hc)) := hassoc.irreducible_iff.2 hirrA
  refine hassoc.prime_iff.1 ?_

  have hprimeω : Prime (weierstrassPoly c hc) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.1 (weierstrassPoly_irreducible c hc hc0 hirrW)
  refine prime_map_of_prime (polyToGerm σ) hprimeω hirrW.ne_zero ?_
    (weierstrassPoly_dvd_of_polyToGerm_dvd c hc hc0)
  intro g
  obtain ⟨g₀, hg₀, hg₀g⟩ := g.2
  obtain ⟨q, a, hq, ha, hdiv⟩ := hD σ d (f ∘ A) g₀ hfA hg₀ hAd
  refine ⟨mkGerm (q * e) (hq.mul he), finPoly fun j => mkGerm (a j) (ha j), Subtype.ext ?_⟩
  rw [Subring.coe_add, Subring.coe_mul, polyToGerm_weierstrassPoly, polyToGerm_finPoly, coe_mkGerm, ← hg₀g,
    ← Germ.coe_mul, ← Germ.coe_add]
  exact Germ.coe_eq.2 (by
    filter_upwards [hdiv, hfe] with x hx hx'
    simp only [Pi.add_apply, Pi.mul_apply]
    rw [hx, hx']
    ring)

/- English proof (translation)
Establish `hG` using `GeneralLinearCoordinates.proof`. Establish `hN` using `AnalyticGermsNoetherian.proof hD hG`. Establish `hfin : ∀ n : ℕ, UniqueFactorizationMonoid (holGerms (0 : Fin n → ℂ))`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Set `_` to `isField_holGerms_fin_zero.toField`. Use `infer_instance`. Consider the case `succ n ih`. Conclude with `(germAffineEquiv (LinearEquiv.funCongrLeft ℂ ℂ (finSuccEquiv n)).toContinuousLinearEquiv (0 : Fin (n + 1) → ℂ)).symm.toMulEquiv.uniqueFactorizationMonoid (uniqueFactorizationMonoid_holGerms_option hN hG hP hD (Fin n) ih)`.

Introduce `σ _ w`. Conclude with `(germAffineEquiv (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv w).symm.toMulEquiv.uniqueFactorizationMonoid (hfin _)`.
-/
theorem HolGermsUFD.proof (hP : WeierstrassPreparation.Statement) (hD : WeierstrassDivision.Statement) :
    HolGermsUFD.Statement := by
  have hG := GeneralLinearCoordinates.proof
  have hN := AnalyticGermsNoetherian.proof hD hG
  have hfin : ∀ n : ℕ, UniqueFactorizationMonoid (holGerms (0 : Fin n → ℂ)) := by
    intro n
    induction n with
    | zero =>
      let _ := isField_holGerms_fin_zero.toField
      infer_instance
    | succ n ih =>
      exact (germAffineEquiv (LinearEquiv.funCongrLeft ℂ ℂ (finSuccEquiv n)).toContinuousLinearEquiv
        (0 : Fin (n + 1) → ℂ)).symm.toMulEquiv.uniqueFactorizationMonoid
        (uniqueFactorizationMonoid_holGerms_option hN hG hP hD (Fin n) ih)
  intro σ _ w
  exact (germAffineEquiv (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ)).toContinuousLinearEquiv
    w).symm.toMulEquiv.uniqueFactorizationMonoid (hfin _)

/- English proof (translation)
The claim follows from `HolGermsUFD.proof (WeierstrassPreparation.proof ParametricCircleIntegralAnalytic.proof CircleArgumentPrinciple.proof PowerSumsEsymmAnalytic.proof) (WeierstrassDivision.proof (WeierstrassPreparation.proof ParametricCircleIntegralAnalytic.proof CircleArgumentPrinciple.proof PowerSu …`.
-/
theorem holGerms_uniqueFactorizationMonoid : HolGermsUFD.Statement :=
  HolGermsUFD.proof
    (WeierstrassPreparation.proof ParametricCircleIntegralAnalytic.proof CircleArgumentPrinciple.proof
      PowerSumsEsymmAnalytic.proof)
    (WeierstrassDivision.proof
      (WeierstrassPreparation.proof ParametricCircleIntegralAnalytic.proof CircleArgumentPrinciple.proof
        PowerSumsEsymmAnalytic.proof)
      (WeierstrassPolynomialDivision.proof ParametricCircleIntegralAnalytic.proof))

instance holGerms_isUFM {σ : Type} [Fintype σ] (w : σ → ℂ) : UniqueFactorizationMonoid (holGerms w) :=
  holGerms_uniqueFactorizationMonoid σ w

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
