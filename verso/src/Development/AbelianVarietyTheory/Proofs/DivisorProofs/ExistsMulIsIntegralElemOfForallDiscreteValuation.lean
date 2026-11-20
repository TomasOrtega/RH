import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Introduce `C B _ _ _ _ e he hloc p hp f hf`. Use `haveI : Nontrivial B := ⟨⟨e 0, e 1, fun h => zero_ne_one (he h)⟩⟩`. Use `haveI : NoZeroDivisors B := ⟨fun {a b} hab => by`. Take `⟨c₁, s₁, u₁, h₁⟩` from `hloc a`. Take `⟨c₂, s₂, u₂, h₂⟩` from `hloc b`.

Establish `hc : c₁ * c₂ = 0` using `he (by`. Rewrite using `[map_mul, ← h₁, ← h₂, map_zero, show a * e s₁ * (b * e s₂) = (a * b) * (e s₁ * e s₂) by ring, hab, zero_mul])`. Break down `mul_eq_zero.1 hc with h | h` into its components or cases. Use `left`. Rewrite `h₁` using `[h, map_zero]`.

Conclude with `u₁.mul_left_eq_zero.1 h₁`. Use `right`. Rewrite `h₂` using `[h, map_zero]`. Conclude with `u₂.mul_left_eq_zero.1 h₂⟩`. Use `haveI : IsDomain B := NoZeroDivisors.to_isDomain B`.

Set `L` to `FractionRing B`. Set `β : B →+* L` to `algebraMap B L`. Establish `hβ : Function.Injective β` using `IsFractionRing.injective B L`. Use `letI : Algebra C L := (β.comp e).toAlgebra`. Establish `hCL : ∀ c, algebraMap C L c = β (e c)` using `fun _ => rfl`.

Establish `hinj : Function.Injective (algebraMap C L)` using `hβ.comp he`. Use `haveI : FaithfulSMul C L := (faithfulSMul_iff_algebraMap_injective C L).2 hinj`. Establish `hne : ∀ s : C, IsUnit (e s) → β (e s) ≠ 0` using `fun s hs => ((hs.map β).ne_zero)`. Use `haveI : IsFractionRing C L := IsFractionRing.of_field C L fun z => by`. Take `⟨x, y, hy, rfl⟩` from `IsFractionRing.div_surjective (A := B) z`.

Take `⟨cx, sx, ux, hx⟩` from `hloc x`. Take `⟨cy, sy, uy, hy'⟩` from `hloc y`. Use `⟨cx * sy, cy * sx, ?_⟩` and prove the remaining obligations. Establish `hy0 : β y ≠ 0`. Rewrite using `[map_ne_zero_iff _ hβ]`.

Conclude with `nonZeroDivisors.ne_zero hy`. Use `show β x / β y = _`. Simplify using `only [hCL, map_mul]`. Rewrite using `[← hx, ← hy']`. Simplify using `only [map_mul]`.

Rewrite using `[div_eq_div_iff hy0 (mul_ne_zero (mul_ne_zero hy0 (hne sy uy)) (hne sx ux))]`. Expand and normalize the polynomial expressions, which then agree. Set `Cp` to `Localization.AtPrime p`. Use `haveI : IsNoetherianRing Cp := IsLocalization.isNoetherianRing p.primeCompl Cp inferInstance`. Establish `hunit : ∀ y : p.primeCompl, IsUnit (algebraMap C L y)` using `fun y => by`.

Use `isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinj).2 ?_)` and prove the remaining obligations. Introduce `h0`. Conclude with `y.2 (h0 ▸ p.zero_mem)`. Use `letI : Algebra Cp L := (IsLocalization.lift (M := p.primeCompl) (S := Cp) hunit).toAlgebra`. Use `haveI : IsScalarTower C Cp L := IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunit x).symm`.

Use `haveI : IsFractionRing Cp L := IsFractionRing.isFractionRing_of_isLocalization p.primeCompl Cp L p.primeCompl_le_nonZeroDivisors`. Use `haveI : Algebra.EssFiniteType Cp L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors Cp)`. Establish `hint : IsIntegral Cp (β f)`. Assume the negation of the conclusion as `hn`. Take `⟨V, hV, hd, hfV⟩` from `exists_discreteValuationSubring_dominating_notMem hn`.

Take `⟨h1, h2⟩` from `(localSubring_range_le_valuationSubring_iff _ V).1 hd`. Apply `hfV` to reduce the goal to its premises. Use `hf L β V hV (fun c => ?_) (fun c hc => ?_)` and prove the remaining obligations. Use `h1 (algebraMap C Cp c)` as an intermediate fact. Rewrite `this` using `[← IsScalarTower.algebraMap_apply]`. Then use the resulting hypothesis.

Use `h2 (algebraMap C Cp c) ((IsLocalization.AtPrime.to_map_mem_maximal_iff Cp p c).2 hc)` as an intermediate fact. Rewrite `this` using `[← IsScalarTower.algebraMap_apply]`. Then use the resulting hypothesis. Take `⟨⟨d, hd⟩, hdi⟩` from `IsIntegral.exists_multiple_integral_of_isLocalization p.primeCompl (β f) hint`. Use `⟨d, hd, ?_⟩` and prove the remaining obligations. Take `⟨q, hq, hq0⟩` from `hdi`.

Use `⟨q, hq, hβ ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.hom_eval₂, map_zero, ← hq0, Submonoid.smul_def, Algebra.smul_def, hCL, map_mul]`. Both sides reduce to the same expression.
-/
theorem exists_mul_isIntegralElem_of_forall_discreteValuationSubring :
    ∀ (C B : Type) [CommRing C] [IsDomain C] [IsNoetherianRing C] [CommRing B] (e : C →+* B),
      Function.Injective e → (∀ b : B, ∃ c s : C, IsUnit (e s) ∧ b * e s = e c) →
      ∀ (p : Ideal C), p.IsPrime → ∀ f : B,
        (∀ (F : Type) [Field F] (β : B →+* F) (V : ValuationSubring F), IsDiscreteValuationRing V →
          (∀ c, β (e c) ∈ V) → (∀ c ∈ p, β (e c) ∈ V.nonunits) → β f ∈ V) →
        ∃ d : C, d ∉ p ∧ e.IsIntegralElem (e d * f) := by
  intro C B _ _ _ _ e he hloc p hp f hf
  haveI : Nontrivial B := ⟨⟨e 0, e 1, fun h => zero_ne_one (he h)⟩⟩
  haveI : NoZeroDivisors B := ⟨fun {a b} hab => by
    obtain ⟨c₁, s₁, u₁, h₁⟩ := hloc a
    obtain ⟨c₂, s₂, u₂, h₂⟩ := hloc b
    have hc : c₁ * c₂ = 0 := he (by
      rw [map_mul, ← h₁, ← h₂, map_zero,
        show a * e s₁ * (b * e s₂) = (a * b) * (e s₁ * e s₂) by ring, hab, zero_mul])
    rcases mul_eq_zero.1 hc with h | h
    · left
      rw [h, map_zero] at h₁
      exact u₁.mul_left_eq_zero.1 h₁
    · right
      rw [h, map_zero] at h₂
      exact u₂.mul_left_eq_zero.1 h₂⟩
  haveI : IsDomain B := NoZeroDivisors.to_isDomain B
  let L := FractionRing B
  let β : B →+* L := algebraMap B L
  have hβ : Function.Injective β := IsFractionRing.injective B L
  letI : Algebra C L := (β.comp e).toAlgebra
  have hCL : ∀ c, algebraMap C L c = β (e c) := fun _ => rfl
  have hinj : Function.Injective (algebraMap C L) := hβ.comp he
  haveI : FaithfulSMul C L := (faithfulSMul_iff_algebraMap_injective C L).2 hinj
  have hne : ∀ s : C, IsUnit (e s) → β (e s) ≠ 0 := fun s hs => ((hs.map β).ne_zero)
  haveI : IsFractionRing C L := IsFractionRing.of_field C L fun z => by
    obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    obtain ⟨cx, sx, ux, hx⟩ := hloc x
    obtain ⟨cy, sy, uy, hy'⟩ := hloc y
    refine ⟨cx * sy, cy * sx, ?_⟩
    have hy0 : β y ≠ 0 := by
      rw [map_ne_zero_iff _ hβ]; exact nonZeroDivisors.ne_zero hy
    show β x / β y = _
    simp only [hCL, map_mul]
    rw [← hx, ← hy']
    simp only [map_mul]
    rw [div_eq_div_iff hy0 (mul_ne_zero (mul_ne_zero hy0 (hne sy uy)) (hne sx ux))]
    ring
  let Cp := Localization.AtPrime p
  haveI : IsNoetherianRing Cp := IsLocalization.isNoetherianRing p.primeCompl Cp inferInstance
  have hunit : ∀ y : p.primeCompl, IsUnit (algebraMap C L y) := fun y => by
    refine isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinj).2 ?_)
    intro h0
    exact y.2 (h0 ▸ p.zero_mem)
  letI : Algebra Cp L := (IsLocalization.lift (M := p.primeCompl) (S := Cp) hunit).toAlgebra
  haveI : IsScalarTower C Cp L :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hunit x).symm
  haveI : IsFractionRing Cp L := IsFractionRing.isFractionRing_of_isLocalization p.primeCompl Cp L
    p.primeCompl_le_nonZeroDivisors
  haveI : Algebra.EssFiniteType Cp L := Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors Cp)
  have hint : IsIntegral Cp (β f) := by
    by_contra hn
    obtain ⟨V, hV, hd, hfV⟩ := exists_discreteValuationSubring_dominating_notMem hn
    obtain ⟨h1, h2⟩ := (localSubring_range_le_valuationSubring_iff _ V).1 hd
    apply hfV
    refine hf L β V hV (fun c => ?_) (fun c hc => ?_)
    · have := h1 (algebraMap C Cp c)
      rwa [← IsScalarTower.algebraMap_apply] at this
    · have := h2 (algebraMap C Cp c)
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff Cp p c).2 hc)
      rwa [← IsScalarTower.algebraMap_apply] at this
  obtain ⟨⟨d, hd⟩, hdi⟩ := IsIntegral.exists_multiple_integral_of_isLocalization p.primeCompl (β f) hint
  refine ⟨d, hd, ?_⟩
  obtain ⟨q, hq, hq0⟩ := hdi
  refine ⟨q, hq, hβ ?_⟩
  rw [Polynomial.hom_eval₂, map_zero, ← hq0, Submonoid.smul_def, Algebra.smul_def, hCL, map_mul]
  rfl

end GlobalTheory
