import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open IsLocalRing in

/- English proof (translation)
Introduce `W K' _ _ _ _ _ _ σ h₁ h₂ l hl`. Establish `inj` using `IsFractionRing.injective W K'`. Use `choose f hf using h₁`. Use `choose g hg using h₂`. Set `F : W →+* W` to `{ toFun := f map_one' := inj (by simp [← hf]) map_mul' := fun x y => inj (by simp [← hf]) map_zero' := inj (by simp [← hf]) map_add' := fun x y => inj (by simp [← hf]) }`.

Set `G : W →+* W` to `{ toFun := g map_one' := inj (by simp [← hg]) map_mul' := fun x y => inj (by simp [← hg]) map_zero' := inj (by simp [← hg]) map_add' := fun x y => inj (by simp [← hg]) }`. Set `τ : W ≃+* W` to `RingEquiv.ofRingHom F G (by ext x; exact inj (by simp [F, G, ← hg, ← hf])) (by ext x; exact inj (by simp [F, G, ← hg, ← hf]))`. Establish `hτ : ∀ x, τ x = f x` using `fun x => rfl`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible W`. Establish `hτϖ : Associated ϖ (τ ϖ)` using `IsDiscreteValuationRing.associated_of_irreducible W hϖ ((MulEquiv.irreducible_iff (f := τ.toMulEquiv)).2 hϖ)`.

Establish `assoc : ∀ x : W, x ≠ 0 → Associated x (f x)`. Introduce `x hx`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ`. Rewrite using `[← hτ, map_mul, map_pow]`. Use `Associated.mul_mul ?_ hτϖ.pow_pow` and prove the remaining obligations.

Conclude with `(associated_one_iff_isUnit.2 u.isUnit).trans (associated_one_iff_isUnit.2 ((Units.map τ.toMonoidHom u).isUnit)).symm`. Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := W) l`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `ha0 : a ≠ 0` using `by rintro rfl; simp at hl`. Take `⟨c, hc⟩` from `assoc a ha0`.

Take `⟨d, hd⟩` from `assoc b hb0`. Use `⟨c * ↑d⁻¹, ?_⟩` and prove the remaining obligations. Establish `hbK : algebraMap W K' b ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb`. Establish `hdK : algebraMap W K' (d : W) * algebraMap W K' (↑d⁻¹ : W) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`.

Rewrite using `[map_div₀, hf, hf, ← hc, ← hd, map_mul, map_mul, map_mul]`. Rewrite using `[eq_inv_of_mul_eq_one_right hdK]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.dvr_fractionField_ringEquiv_eq_mul :
    ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (σ : K' ≃+* K'), (∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → ∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l := by
  intro W K' _ _ _ _ _ _ σ h₁ h₂ l hl
  classical
  have inj := IsFractionRing.injective W K'
  choose f hf using h₁
  choose g hg using h₂
  let F : W →+* W :=
    { toFun := f
      map_one' := inj (by simp [← hf])
      map_mul' := fun x y => inj (by simp [← hf])
      map_zero' := inj (by simp [← hf])
      map_add' := fun x y => inj (by simp [← hf]) }
  let G : W →+* W :=
    { toFun := g
      map_one' := inj (by simp [← hg])
      map_mul' := fun x y => inj (by simp [← hg])
      map_zero' := inj (by simp [← hg])
      map_add' := fun x y => inj (by simp [← hg]) }
  let τ : W ≃+* W := RingEquiv.ofRingHom F G
    (by ext x; exact inj (by simp [F, G, ← hg, ← hf]))
    (by ext x; exact inj (by simp [F, G, ← hg, ← hf]))
  have hτ : ∀ x, τ x = f x := fun x => rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hτϖ : Associated ϖ (τ ϖ) :=
    IsDiscreteValuationRing.associated_of_irreducible W hϖ
      ((MulEquiv.irreducible_iff (f := τ.toMulEquiv)).2 hϖ)
  have assoc : ∀ x : W, x ≠ 0 → Associated x (f x) := by
    intro x hx
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
    rw [← hτ, map_mul, map_pow]
    refine Associated.mul_mul ?_ hτϖ.pow_pow
    exact (associated_one_iff_isUnit.2 u.isUnit).trans
      (associated_one_iff_isUnit.2 ((Units.map τ.toMonoidHom u).isUnit)).symm
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) l
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hl
  obtain ⟨c, hc⟩ := assoc a ha0
  obtain ⟨d, hd⟩ := assoc b hb0
  refine ⟨c * ↑d⁻¹, ?_⟩
  have hbK : algebraMap W K' b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hdK : algebraMap W K' (d : W) * algebraMap W K' (↑d⁻¹ : W) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [map_div₀, hf, hf, ← hc, ← hd, map_mul, map_mul, map_mul]
  rw [eq_inv_of_mul_eq_one_right hdK]
  ring

end GlobalTheory
