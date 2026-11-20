import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Introduce `H U V _ _ _ _ _ _ ρ σ f hf hsurj`. Use `haveI := Fintype.ofFinite H`. Take `⟨s₀, hs₀⟩` from `f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)`. Establish `hs₀' : ∀ y, f (s₀ y) = y` using `fun y => LinearMap.congr_fun hs₀ y`. Establish `hc : (Fintype.card H : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`.

Establish `hρ : ∀ (a b : H) (x : U), ρ (a * b) x = ρ a (ρ b x)` using `fun a b x => by`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Establish `hσ : ∀ (a b : H) (x : V), σ (a * b) x = σ a (σ b x)` using `fun a b x => by`. Rewrite using `[map_mul]`.

Both sides reduce to the same expression. Establish `hσ1 : ∀ x : V, σ 1 x = x` using `fun x => by`. Rewrite using `[map_one]`. Both sides reduce to the same expression. Use `⟨(Fintype.card H : ℂ)⁻¹ • ∑ g : H, (ρ g) ∘ₗ s₀ ∘ₗ (σ g⁻¹), ?_, ?_⟩` and prove the remaining obligations.

Introduce `h x`. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]`. Use `congr 1`. Use `Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv]`.

Rewrite using `[← hρ, mul_inv_cancel_left, hσ]`. Introduce `x`. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]`. Establish `: ∀ g : H, f (ρ g (s₀ (σ g⁻¹ x))) = x` using `fun g => by`. Rewrite using `[hf, hs₀', ← hσ, mul_inv_cancel, hσ1]`.

Simplify using `only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]`. Rewrite using `[← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]`.
-/
theorem UpperTheory.Gal.InertialTypesAlt.finSec :
    FinSec := by
  intro H U V _ _ _ _ _ _ ρ σ f hf hsurj
  haveI := Fintype.ofFinite H
  obtain ⟨s₀, hs₀⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hsurj)
  have hs₀' : ∀ y, f (s₀ y) = y := fun y => LinearMap.congr_fun hs₀ y
  have hc : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hρ : ∀ (a b : H) (x : U), ρ (a * b) x = ρ a (ρ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hσ : ∀ (a b : H) (x : V), σ (a * b) x = σ a (σ b x) := fun a b x => by
    rw [map_mul]; rfl
  have hσ1 : ∀ x : V, σ 1 x = x := fun x => by
    rw [map_one]; rfl
  refine ⟨(Fintype.card H : ℂ)⁻¹ • ∑ g : H, (ρ g) ∘ₗ s₀ ∘ₗ (σ g⁻¹), ?_, ?_⟩
  · intro h x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_inv]
    rw [← hρ, mul_inv_cancel_left, hσ]
  · intro x
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply, map_smul, map_sum]
    have : ∀ g : H, f (ρ g (s₀ (σ g⁻¹ x))) = x := fun g => by
      rw [hf, hs₀', ← hσ, mul_inv_cancel, hσ1]
    simp only [this, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
