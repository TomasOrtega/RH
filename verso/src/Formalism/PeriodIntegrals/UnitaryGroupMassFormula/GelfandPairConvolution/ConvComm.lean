import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandPairConvolution.Unimod

noncomputable section

namespace PI.UnitaryGroupMassFormula.GelfConv

open MeasureTheory Measure

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ μ _ H τ hc hm hi hconj f₁ f₂ _ _ hf₁ hf₂ z`. Use `isMulRightInvariant_of_compact μ` as an intermediate fact. Use `isInvInvariant_of_compact μ` as an intermediate fact. Establish `h1 : τ 1 = 1`. Use `hm 1 1` as an intermediate fact.

Simplify using `only [mul_one] at this`. Conclude with `(mul_eq_left.mp this.symm)`. Establish `hinv : ∀ x, τ x⁻¹ = (τ x)⁻¹` using `fun x => by`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← hm, mul_inv_cancel, h1]`.

Establish `hτ₁ : ∀ x, f₁ (τ x) = f₁ x` using `fun x => by`. Take `⟨h, hH, e⟩` from `hconj x`. Rewrite using `[e, hf₁ h hH]`. Establish `hτ₂ : ∀ x, f₂ (τ x) = f₂ x` using `fun x => by`. Take `⟨h, hH, e⟩` from `hconj x`.

Rewrite using `[e, hf₂ h hH]`. Establish `hF : ∀ h ∈ H, ∀ w, ∫ x, f₁ x * f₂ (x⁻¹ * (h * w * h⁻¹)) ∂μ = ∫ x, f₁ x * f₂ (x⁻¹ * w) ∂μ`. Introduce `h hH w`. Establish `e` using `integral_comp_homeo μ ((Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹)) (measurePreserving_conj μ h) (fun x => f₁ x * f₂ (x⁻¹ * (h * w * h⁻¹)))`. Rewrite using `[← e]`.

Use `congr 1`. Use function extensionality and compare the values at `y`. Simplify using `only [Homeomorph.trans_apply, Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight]`. Rewrite using `[hf₁ h hH]`. Establish `: (h * y * h⁻¹)⁻¹ * (h * w * h⁻¹) = h * (y⁻¹ * w) * h⁻¹` using `by group`.

Rewrite using `[this, hf₂ h hH]`. Set `eτ : G ≃ₜ G` to `{ toFun := τ, invFun := τ, left_inv := hi, right_inv := hi, continuous_toFun := hc, continuous_invFun := hc }`. Establish `hτμ : MeasurePreserving eτ μ μ` using `measurePreserving_anti μ τ hc hm hi`. Take `⟨h, hH, ez⟩` from `hconj z`. Establish `A : ∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ = ∫ x, f₁ x * f₂ (x⁻¹ * τ z) ∂μ`.

Rewrite using `[ez, hF h hH]`. Establish `B : ∫ x, f₁ x * f₂ (x⁻¹ * τ z) ∂μ = ∫ y, f₁ y * f₂ (z * y⁻¹) ∂μ`. Rewrite using `[← integral_comp_homeo μ eτ hτμ (fun x => f₁ x * f₂ (x⁻¹ * τ z))]`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Express the relevant statement in the definitionally equal form `f₁ (τ y) * f₂ ((τ y)⁻¹ * τ z) = f₁ y * f₂ (z * y⁻¹)`. Rewrite using `[← hinv, ← hm, hτ₁, hτ₂]`. Establish `C : ∫ y, f₁ y * f₂ (z * y⁻¹) ∂μ = ∫ x, f₂ x * f₁ (x⁻¹ * z) ∂μ`. Establish `e1` using `integral_mul_right_eq_self (μ := μ) (fun y => f₁ y * f₂ (z * y⁻¹)) z`. Establish `e2` using `integral_inv_eq_self (fun w => f₁ (w * z) * f₂ (z * (w * z)⁻¹)) μ`.

Rewrite using `[← e1, ← e2]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Establish `: z * (w⁻¹ * z)⁻¹ = w` using `by group`. Simplify using `only [this, mul_comm]`.

Rewrite using `[A, B, C]`.
-/
theorem convComm : PI.UMultOne.ConvComm := by
  intro G _ _ _ _ _ _ _ _ μ _ H τ hc hm hi hconj f₁ f₂ _ _ hf₁ hf₂ z
  have := isMulRightInvariant_of_compact μ
  have := isInvInvariant_of_compact μ
  have h1 : τ 1 = 1 := by
    have := hm 1 1
    simp only [mul_one] at this
    exact (mul_eq_left.mp this.symm)
  have hinv : ∀ x, τ x⁻¹ = (τ x)⁻¹ := fun x => by
    apply eq_inv_of_mul_eq_one_left
    rw [← hm, mul_inv_cancel, h1]

  have hτ₁ : ∀ x, f₁ (τ x) = f₁ x := fun x => by
    obtain ⟨h, hH, e⟩ := hconj x
    rw [e, hf₁ h hH]
  have hτ₂ : ∀ x, f₂ (τ x) = f₂ x := fun x => by
    obtain ⟨h, hH, e⟩ := hconj x
    rw [e, hf₂ h hH]

  have hF : ∀ h ∈ H, ∀ w, ∫ x, f₁ x * f₂ (x⁻¹ * (h * w * h⁻¹)) ∂μ = ∫ x, f₁ x * f₂ (x⁻¹ * w) ∂μ := by
    intro h hH w
    have e := integral_comp_homeo μ ((Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹))
      (measurePreserving_conj μ h)
      (fun x => f₁ x * f₂ (x⁻¹ * (h * w * h⁻¹)))
    rw [← e]
    congr 1
    funext y
    simp only [Homeomorph.trans_apply, Homeomorph.coe_mulLeft, Homeomorph.coe_mulRight]
    rw [hf₁ h hH]
    have : (h * y * h⁻¹)⁻¹ * (h * w * h⁻¹) = h * (y⁻¹ * w) * h⁻¹ := by group
    rw [this, hf₂ h hH]

  let eτ : G ≃ₜ G :=
    { toFun := τ, invFun := τ, left_inv := hi, right_inv := hi,
      continuous_toFun := hc, continuous_invFun := hc }
  have hτμ : MeasurePreserving eτ μ μ := measurePreserving_anti μ τ hc hm hi
  obtain ⟨h, hH, ez⟩ := hconj z

  have A : ∫ x, f₁ x * f₂ (x⁻¹ * z) ∂μ = ∫ x, f₁ x * f₂ (x⁻¹ * τ z) ∂μ := by
    rw [ez, hF h hH]

  have B : ∫ x, f₁ x * f₂ (x⁻¹ * τ z) ∂μ = ∫ y, f₁ y * f₂ (z * y⁻¹) ∂μ := by
    rw [← integral_comp_homeo μ eτ hτμ (fun x => f₁ x * f₂ (x⁻¹ * τ z))]
    congr 1
    funext y
    change f₁ (τ y) * f₂ ((τ y)⁻¹ * τ z) = f₁ y * f₂ (z * y⁻¹)
    rw [← hinv, ← hm, hτ₁, hτ₂]

  have C : ∫ y, f₁ y * f₂ (z * y⁻¹) ∂μ = ∫ x, f₂ x * f₁ (x⁻¹ * z) ∂μ := by
    have e1 := integral_mul_right_eq_self (μ := μ) (fun y => f₁ y * f₂ (z * y⁻¹)) z
    have e2 := integral_inv_eq_self (fun w => f₁ (w * z) * f₂ (z * (w * z)⁻¹)) μ
    rw [← e1, ← e2]
    congr 1
    funext w
    have : z * (w⁻¹ * z)⁻¹ = w := by group
    simp only [this, mul_comm]
  rw [A, B, C]

end PI.UnitaryGroupMassFormula.GelfConv
