import Mathlib

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Establish `hv : σ g (σ g⁻¹ v) = v`. Rewrite using `[← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]`. Set `f : H →ₗᵢ[ℂ] H` to `{ toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hσ g }`. Establish `hf : ∀ x, f x = σ g x` using `fun _ => rfl`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem inner_isometricRep_inv {G : Type} [Group G] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (g : G) (u v : H) : ⟪u, σ g⁻¹ v⟫_ℂ = ⟪σ g u, v⟫_ℂ := by
  have hv : σ g (σ g⁻¹ v) = v := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  let f : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hσ g }
  have hf : ∀ x, f x = σ g x := fun _ => rfl
  calc ⟪u, σ g⁻¹ v⟫_ℂ = ⟪f u, f (σ g⁻¹ v)⟫_ℂ := (f.inner_map_map _ _).symm
    _ = ⟪σ g u, v⟫_ℂ := by rw [hf, hf, hv]

/- English proof (translation)
Introduce `G _ _ μ H _ _ _ σ d hd hσ hS w hw`. Establish `adj : ∀ (g : G) (a b : H), ⟪a, σ g⁻¹ b⟫_ℂ = ⟪σ g a, b⟫_ℂ` using `fun g a b => inner_isometricRep_inv σ hσ g a b`. Establish `hc : ∀ a b : H, star ⟪a, b⟫_ℂ = ⟪b, a⟫_ℂ` using `fun a b => by`. Rewrite using `[← starRingEnd_apply, inner_conj_symm]`. Establish `hd0 : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`.

Establish `hdc : star (d : ℂ) = d` using `by simp`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`. Rewrite using `[star_mul', star_star, hdc, adj, hc]`. Introduce `x y`.

Establish `key : ∀ g : G, star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ = ⟪σ y w, σ g (σ x w)⟫_ℂ`. Introduce `g`. Rewrite using `[map_mul, map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, adj, adj, hc]`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Use function extensionality and compare the values at `g`. Rewrite using `[key]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ((d : ℂ) * d) * (⟪w, σ x w⟫_ℂ * ⟪σ y w, w⟫_ℂ / d) := by`. Rewrite using `[integral_const_mul, hS]`.

Use `_ = ⟪w, σ x w⟫_ℂ * ((d : ℂ) * star ⟪w, σ y w⟫_ℂ) := by`. Rewrite using `[hc]`. Clear the denominators using the available nonvanishing facts. Introduce `u u'`. Combine the equalities or inequalities in the displayed calculation.

Use `congr 1`. Use function extensionality and compare the values at `g`. Expand and normalize the polynomial expressions, which then agree. Use `_ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ := by`. Rewrite using `[integral_const_mul, hS]`.

Clear the denominators using the available nonvanishing facts. Introduce `y hy`. Establish `h0` using `hS w y w y`. Simplify using `only [hy, zero_mul, integral_zero] at h0`. Establish `hww : ⟪w, w⟫_ℂ = 1` using `by rw [inner_self_eq_norm_sq_to_K, hw]; simp`.

Rewrite `h0` using `[hww, one_mul]`. Establish `hyy : ⟪y, y⟫_ℂ = 0` using `(div_eq_zero_iff.mp h0.symm).resolve_right hd0`. Conclude with `inner_self_eq_zero.mp hyy`.
-/
theorem matrixCoeff_idempotent_of_orthogonality : ∀ (G : Type) [Group G] [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (d : ℝ), 0 < d → (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ v w v' w' : H, ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) → ∀ w : H, ‖w‖ = 1 → (∀ g : G, star ((d : ℂ) * star ⟪w, σ g⁻¹ w⟫_ℂ) = (d : ℂ) * star ⟪w, σ g w⟫_ℂ) ∧ (∀ x y : G, ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ((d : ℂ) * star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ) ∂μ = ⟪w, σ x w⟫_ℂ * ((d : ℂ) * star ⟪w, σ y w⟫_ℂ)) ∧ (∀ u u' : H, ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ⟪u', σ g u⟫_ℂ ∂μ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ) ∧ ∀ y : H, (∀ g, ⟪y, σ g w⟫_ℂ = 0) → y = 0 := by
  intro G _ _ μ H _ _ _ σ d hd hσ hS w hw
  have adj : ∀ (g : G) (a b : H), ⟪a, σ g⁻¹ b⟫_ℂ = ⟪σ g a, b⟫_ℂ :=
    fun g a b => inner_isometricRep_inv σ hσ g a b
  have hc : ∀ a b : H, star ⟪a, b⟫_ℂ = ⟪b, a⟫_ℂ := fun a b => by
    rw [← starRingEnd_apply, inner_conj_symm]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdc : star (d : ℂ) = d := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    rw [star_mul', star_star, hdc, adj, hc]
  · intro x y
    have key : ∀ g : G, star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ = ⟪σ y w, σ g (σ x w)⟫_ℂ := by
      intro g
      rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
        adj, adj, hc]
    calc ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ((d : ℂ) * star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ) ∂μ
        = ∫ g, ((d : ℂ) * d) * (⟪σ y w, σ g (σ x w)⟫_ℂ * star ⟪w, σ g w⟫_ℂ) ∂μ := by
          congr 1; funext g; rw [key]; ring
      _ = ((d : ℂ) * d) * (⟪w, σ x w⟫_ℂ * ⟪σ y w, w⟫_ℂ / d) := by
          rw [integral_const_mul, hS]
      _ = ⟪w, σ x w⟫_ℂ * ((d : ℂ) * star ⟪w, σ y w⟫_ℂ) := by
          rw [hc]; field_simp
  · intro u u'
    calc ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ⟪u', σ g u⟫_ℂ ∂μ
        = ∫ g, (d : ℂ) * (⟪u', σ g u⟫_ℂ * star ⟪w, σ g w⟫_ℂ) ∂μ := by
          congr 1; funext g; ring
      _ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ := by
          rw [integral_const_mul, hS]; field_simp
  · intro y hy
    have h0 := hS w y w y
    simp only [hy, zero_mul, integral_zero] at h0
    have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
    rw [hww, one_mul] at h0
    have hyy : ⟪y, y⟫_ℂ = 0 := (div_eq_zero_iff.mp h0.symm).resolve_right hd0
    exact inner_self_eq_zero.mp hyy

end GlobalTheory
