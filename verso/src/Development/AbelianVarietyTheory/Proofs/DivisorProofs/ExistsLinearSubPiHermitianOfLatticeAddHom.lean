import Mathlib
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.AppellHumbertNormalFormOfLinearExponent

open Complex Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `g Λ H _ hΛ hH p`. Take `⟨F, hF⟩` from `AppellHumbert.exists_real_extension Λ hΛ p`. Establish `hinj : Function.Injective H.vecMulLinear`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`.

Assume the negation of the conclusion as `h0`. Use `hH v h0` as an intermediate fact. Rewrite `this` using `[dotProduct_mulVec]`. Rewrite `hv` using `[vecMulLinear_apply]`. Simplify using `[hv] at this`.

Establish `hsurj` using `LinearMap.injective_iff_surjective.1 hinj`. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`. Set `s : Fin g → ℂ` to `fun b => (F (Pi.single b 1) - I * F (Pi.single b I)) / 2`. Set `c : Fin g → ℂ` to `fun b => (F (Pi.single b 1) + I * F (Pi.single b I)) / 2`. Establish `hsplit : ∀ u, F u = s ⬝ᵥ u + c ⬝ᵥ star u`.

Introduce `u`. Use `conv_lhs => rw [AppellHumbert.eq_sum_re_im u]`. Simplify using `only [map_sum, map_add, map_smul, dotProduct, ← Finset.sum_add_distrib, Pi.star_apply, real_smul, s, c]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `h1 : u b = (u b).re + (u b).im * I` using `(re_add_im _).symm`.

Establish `h2 : star (u b) = (u b).re - (u b).im * I`. Apply the tactic sequence `apply Complex.ext <;> simp`. Rewrite using `[h2]`. Generalize the expression as in `(u b).re = x at *`. Generalize the expression as in `(u b).im = y at *`.

Rewrite using `[h1]`. Take the linear combination `(y * F (Pi.single b I)) * I_mul_I`. Take `⟨v, hv⟩` from `hsurj (-(Real.pi : ℂ)⁻¹ • c)`. Rewrite `hv` using `[vecMulLinear_apply]`. Use `⟨LinearMap.toContinuousLinearMap (dotProductBilin ℂ ℂ s), v, fun l => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hF, hsplit, dotProduct_mulVec, hv, smul_dotProduct]`. Simplify using `only [LinearMap.coe_toContinuousLinearMap', dotProductBilin_apply_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_linear_sub_pi_mul_form_of_addMonoidHom :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (H : Matrix (Fin g) (Fin g) ℂ), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H.mulVec (star z)).re) → ∀ p : Λ →+ ℂ, ∃ (f : (Fin g → ℂ) →L[ℂ] ℂ) (v : Fin g → ℂ), ∀ l : Λ, p l = f l - Real.pi * (v ⬝ᵥ H.mulVec (star (l : Fin g → ℂ))) := by
  intro g Λ H _ hΛ hH p
  obtain ⟨F, hF⟩ := AppellHumbert.exists_real_extension Λ hΛ p
  have hinj : Function.Injective H.vecMulLinear := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra h0
    have := hH v h0
    rw [dotProduct_mulVec] at this
    rw [vecMulLinear_apply] at hv
    simp [hv] at this
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  let s : Fin g → ℂ := fun b => (F (Pi.single b 1) - I * F (Pi.single b I)) / 2
  let c : Fin g → ℂ := fun b => (F (Pi.single b 1) + I * F (Pi.single b I)) / 2
  have hsplit : ∀ u, F u = s ⬝ᵥ u + c ⬝ᵥ star u := by
    intro u
    conv_lhs => rw [AppellHumbert.eq_sum_re_im u]
    simp only [map_sum, map_add, map_smul, dotProduct, ← Finset.sum_add_distrib,
      Pi.star_apply, real_smul, s, c]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 : u b = (u b).re + (u b).im * I := (re_add_im _).symm
    have h2 : star (u b) = (u b).re - (u b).im * I := by
      apply Complex.ext <;> simp
    rw [h2]
    generalize (u b).re = x at *
    generalize (u b).im = y at *
    rw [h1]
    linear_combination (y * F (Pi.single b I)) * I_mul_I
  obtain ⟨v, hv⟩ := hsurj (-(Real.pi : ℂ)⁻¹ • c)
  rw [vecMulLinear_apply] at hv
  refine ⟨LinearMap.toContinuousLinearMap (dotProductBilin ℂ ℂ s), v, fun l => ?_⟩
  rw [← hF, hsplit, dotProduct_mulVec, hv, smul_dotProduct]
  simp only [LinearMap.coe_toContinuousLinearMap', dotProductBilin_apply_apply, smul_eq_mul]
  field_simp
  ring

end GlobalTheory
