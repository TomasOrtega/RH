import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivTruncExpICompLe
open SchwartzMap Filter Topology
open scoped Nat
noncomputable section
namespace GlobalTheory

/- English proof (translation)
Introduce `V _ _ _ Q c hc hQ b k B`. Set `Qc : V →L[ℝ] V →L[ℝ] ℂ` to `-LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ Q)`. Establish `hQc : ∀ y, Qc y y = -(Q y y)` using `fun y => rfl`. Establish `hfun : (fun y => Complex.exp (-(Q y y))) = fun y => Complex.exp (Qc y y)`. Use function extensionality and compare the values at `y`.

Rewrite using `[hQc]`. Establish `hB' : ∀ x, (Qc x x).re ≤ -(c * ‖x‖ ^ 2)`. Introduce `x`. Rewrite using `[hQc, Complex.neg_re]`. Combine the linear relations using `[hQ x]`.

Take `⟨C0, hC0⟩` from `GaussExpSeries.exists_bound_poly_mul_exp (c / 2) (by positivity) (k + 2 * b)`. Use `⟨(b ! * (2 * (‖Qc‖ + 1)) ^ b) * Real.exp (B ^ 2 / (2 * c)) * C0, fun x => ?_⟩` and prove the remaining obligations. Establish `hr0 : 0 ≤ ‖x‖` using `norm_nonneg x`. Establish `hD` using `GaussExpSeries.norm_iteratedFDeriv_gauss_le Qc c hB' b x`. Rewrite using `[hfun]`.

Establish `hpow : ‖x‖ ^ k * (1 + ‖x‖) ^ (2 * b) ≤ (1 + ‖x‖) ^ (k + 2 * b)`. Rewrite using `[pow_add]`. Use `gcongr`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hexp : Real.exp (B * ‖x‖) * Real.exp (-(c * ‖x‖ ^ 2)) ≤ Real.exp (B ^ 2 / (2 * c)) * Real.exp (-(c / 2 * ‖x‖ ^ 2))`.

Rewrite using `[← Real.exp_add, ← Real.exp_add]`. Apply `Real.exp_le_exp.2` to reduce the goal to its premises. Establish `h1 : B ^ 2 / (2 * c) + -(c / 2 * ‖x‖ ^ 2) - (B * ‖x‖ + -(c * ‖x‖ ^ 2)) = (c * ‖x‖ - B) ^ 2 / (2 * c)` using `by field_simp; ring`. Establish `h2 : 0 ≤ (c * ‖x‖ - B) ^ 2 / (2 * c)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hC0'` using `hC0 ‖x‖ hr0`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, pow_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (b ! * (2 * (‖Qc‖ + 1)) ^ b) * ((1 + ‖x‖) ^ (k + 2 * b) * (Real.exp (B ^ 2 / (2 * c)) * Real.exp (-(c / 2 * ‖x‖ ^ 2)))) := by gcongr`.

Use `_ = (b ! * (2 * (‖Qc‖ + 1)) ^ b) * Real.exp (B ^ 2 / (2 * c)) * ((1 + ‖x‖) ^ (k + 2 * b) * Real.exp (-(c / 2 * ‖x‖ ^ 2))) := by ring`. Use `_ ≤ (b ! * (2 * (‖Qc‖ + 1)) ^ b) * Real.exp (B ^ 2 / (2 * c)) * C0 := by gcongr`.
-/
theorem gauss_weighted_iteratedFDeriv_bounded : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (Q : V →ₗ[ℝ] V →ₗ[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∀ (b k : ℕ) (B : ℝ), ∃ C : ℝ, ∀ x : V,
      ‖x‖ ^ k * Real.exp (B * ‖x‖) * ‖iteratedFDeriv ℝ b (fun y => Complex.exp (-(Q y y))) x‖ ≤ C := by
  intro V _ _ _ Q c hc hQ b k B
  let Qc : V →L[ℝ] V →L[ℝ] ℂ := -LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℂ) ≃ₗ[ℝ] (V →L[ℝ] ℂ)).toLinearMap ∘ₗ Q)
  have hQc : ∀ y, Qc y y = -(Q y y) := fun y => rfl
  have hfun : (fun y => Complex.exp (-(Q y y))) = fun y => Complex.exp (Qc y y) := by
    funext y; rw [hQc]
  have hB' : ∀ x, (Qc x x).re ≤ -(c * ‖x‖ ^ 2) := by
    intro x; rw [hQc, Complex.neg_re]; linarith [hQ x]
  obtain ⟨C0, hC0⟩ := GaussExpSeries.exists_bound_poly_mul_exp (c / 2) (by positivity) (k + 2 * b)
  refine ⟨(b ! * (2 * (‖Qc‖ + 1)) ^ b) * Real.exp (B ^ 2 / (2 * c)) * C0, fun x => ?_⟩
  have hr0 : 0 ≤ ‖x‖ := norm_nonneg x
  have hD := GaussExpSeries.norm_iteratedFDeriv_gauss_le Qc c hB' b x
  rw [hfun]
  have hpow : ‖x‖ ^ k * (1 + ‖x‖) ^ (2 * b) ≤ (1 + ‖x‖) ^ (k + 2 * b) := by
    rw [pow_add]; gcongr; linarith
  have hexp : Real.exp (B * ‖x‖) * Real.exp (-(c * ‖x‖ ^ 2)) ≤
      Real.exp (B ^ 2 / (2 * c)) * Real.exp (-(c / 2 * ‖x‖ ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : B ^ 2 / (2 * c) + -(c / 2 * ‖x‖ ^ 2) - (B * ‖x‖ + -(c * ‖x‖ ^ 2)) =
        (c * ‖x‖ - B) ^ 2 / (2 * c) := by
      field_simp; ring
    have h2 : 0 ≤ (c * ‖x‖ - B) ^ 2 / (2 * c) := by positivity
    linarith
  have hC0' := hC0 ‖x‖ hr0
  calc ‖x‖ ^ k * Real.exp (B * ‖x‖) * ‖iteratedFDeriv ℝ b (fun y => Complex.exp (Qc y y)) x‖
      ≤ ‖x‖ ^ k * Real.exp (B * ‖x‖) *
          (b ! * Real.exp (-(c * ‖x‖ ^ 2)) * (2 * (‖Qc‖ + 1) * (1 + ‖x‖) ^ 2) ^ b) := by
        gcongr
    _ = (b ! * (2 * (‖Qc‖ + 1)) ^ b) * ((‖x‖ ^ k * (1 + ‖x‖) ^ (2 * b)) *
          (Real.exp (B * ‖x‖) * Real.exp (-(c * ‖x‖ ^ 2)))) := by
        rw [mul_pow, pow_mul]; ring
    _ ≤ (b ! * (2 * (‖Qc‖ + 1)) ^ b) * ((1 + ‖x‖) ^ (k + 2 * b) *
          (Real.exp (B ^ 2 / (2 * c)) * Real.exp (-(c / 2 * ‖x‖ ^ 2)))) := by
        gcongr
    _ = (b ! * (2 * (‖Qc‖ + 1)) ^ b) * Real.exp (B ^ 2 / (2 * c)) *
          ((1 + ‖x‖) ^ (k + 2 * b) * Real.exp (-(c / 2 * ‖x‖ ^ 2))) := by ring
    _ ≤ (b ! * (2 * (‖Qc‖ + 1)) ^ b) * Real.exp (B ^ 2 / (2 * c)) * C0 := by gcongr

end GlobalTheory
