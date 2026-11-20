import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `K κ _ _ _ _ R π hR hc hsurj hinj`. Use `haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr Subtype.val_injective`. Use `haveI : IsFractionRing R K := IsFractionRing.of_field R K (fun z => by`. Take `⟨a, ha, b, hb, hb0, e⟩` from `hR.frac z`. Use `⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `z = a / b`. Rewrite using `[eq_div_iff hb0, e])`. Set `φ : K →+* κ` to `IsFractionRing.lift hinj`. Establish `hφ : ∀ r : R, φ (algebraMap R K r) = π r` using `fun r => IsFractionRing.lift_algebraMap hinj r`. Establish `hφc : ∀ a : ℂ, φ (algebraMap ℂ K a) = algebraMap ℂ κ a`.

Introduce `a`. Use `hφ ⟨algebraMap ℂ K a, hR.const_mem a⟩` as an intermediate fact. Rewrite using `[← hc a (hR.const_mem a)]`. Conclude with `this`. Set `ψ : K →ₐ[ℂ] κ` to `{ φ with commutes' := hφc }`.

Establish `hbij : Function.Bijective ψ`. Use `⟨ψ.toRingHom.injective, fun f => ?_⟩` and prove the remaining obligations. Take `⟨a, b, hb, e⟩` from `hsurj f`. Establish `hb' : (b : K) ≠ 0`. Introduce `h`.

Apply `hb` to reduce the goal to its premises. Establish `: b = 0` using `Subtype.ext h`. Rewrite using `[this, map_zero]`. Use `⟨(a : K) / b, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `φ ((a : K) / b) = f`.

Rewrite using `[map_div₀]`. Establish `ha` using `hφ a`. Establish `hb2` using `hφ b`. Express the relevant statement in the definitionally equal form `φ (a : K) = π a at ha`. Express the relevant statement in the definitionally equal form `φ (b : K) = π b at hb2`.

Rewrite using `[ha, hb2, div_eq_iff hb, e]`. Use `⟨AlgEquiv.ofBijective ψ hbij, fun r => ?_⟩` and prove the remaining obligations. Conclude with `hφ r`.
-/
theorem locModel_fracField_algEquiv : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ]
  (R : Subring K) (π : R →+* κ), IsLocModel (algebraMap ℂ K) R →
  (∀ a (h : algebraMap ℂ K a ∈ R), π ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → Function.Injective π →
  ∃ e : K ≃ₐ[ℂ] κ, ∀ r : R, e r = π r := by
  intro K κ _ _ _ _ R π hR hc hsurj hinj
  haveI : FaithfulSMul R K :=
    (faithfulSMul_iff_algebraMap_injective R K).mpr Subtype.val_injective
  haveI : IsFractionRing R K := IsFractionRing.of_field R K (fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hR.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change z = a / b
    rw [eq_div_iff hb0, e])
  let φ : K →+* κ := IsFractionRing.lift hinj
  have hφ : ∀ r : R, φ (algebraMap R K r) = π r := fun r => IsFractionRing.lift_algebraMap hinj r
  have hφc : ∀ a : ℂ, φ (algebraMap ℂ K a) = algebraMap ℂ κ a := by
    intro a
    have := hφ ⟨algebraMap ℂ K a, hR.const_mem a⟩
    rw [← hc a (hR.const_mem a)]
    exact this
  let ψ : K →ₐ[ℂ] κ := { φ with commutes' := hφc }
  have hbij : Function.Bijective ψ := by
    refine ⟨ψ.toRingHom.injective, fun f => ?_⟩
    obtain ⟨a, b, hb, e⟩ := hsurj f
    have hb' : (b : K) ≠ 0 := by
      intro h
      apply hb
      have : b = 0 := Subtype.ext h
      rw [this, map_zero]
    refine ⟨(a : K) / b, ?_⟩
    change φ ((a : K) / b) = f
    rw [map_div₀]
    have ha := hφ a
    have hb2 := hφ b
    change φ (a : K) = π a at ha
    change φ (b : K) = π b at hb2
    rw [ha, hb2, div_eq_iff hb, e]
  refine ⟨AlgEquiv.ofBijective ψ hbij, fun r => ?_⟩
  exact hφ r

end GlobalTheory
