import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane Filter Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm
open scoped Manifold Pointwise

namespace GlobalTheory.HeckeFamilyMatrices

/- English proof (translation)
Take `⟨c, hc, hd⟩` from `CuspFormClass.exp_decay_atImInfty' (Γ := G) (k := k) g`. Take `⟨C₀, hC₀⟩` from `CuspFormClass.petersson_bounded_left k G g g`. Take `⟨D, hD, h⟩` from `hd.exists_pos`. Rewrite `h` using `[Asymptotics.IsBigOWith, atImInfty, eventually_comap, eventually_atTop]`. Take `⟨y, hy⟩` from `h`.

Establish `hC₀0 : 0 ≤ C₀` using `le_trans (norm_nonneg _) (hC₀ UpperHalfPlane.I)`. Use `set M : ℝ := 1 + C₀ * |y| ^ k.natAbs with hM`. Establish `hM0 : 0 ≤ M` using `by positivity`. Use `⟨max D (M * Real.exp (c * |y|)), c, hc, fun τ hτ => ?_⟩` and prove the remaining obligations. Break down `le_total y τ.im with h1 | h1` into its components or cases.

Establish `h2` using `hy _ h1 τ rfl`. Rewrite `h2` using `[Real.norm_of_nonneg (Real.exp_pos _).le]`. Conclude with `h2.trans (by gcongr; exact le_max_left _ _)`. Establish `hy' : τ.im ≤ |y|` using `h1.trans (le_abs_self y)`. Establish `hp : ‖g τ‖ ^ 2 * τ.im ^ k ≤ C₀`.

Use `hC₀ τ` as an intermediate fact. Simplify using `only [UpperHalfPlane.petersson, norm_mul, Complex.norm_conj, norm_zpow, Complex.norm_real, Real.norm_of_nonneg τ.im_pos.le] at this`. Combine the equalities or inequalities in the displayed calculation. Establish `hpos` using `τ.im_pos`. Establish `hk : 1 ≤ τ.im ^ k * τ.im ^ k.natAbs`.

Rewrite using `[← zpow_natCast, ← zpow_add₀ hpos.ne']`. Conclude with `one_le_zpow₀ hτ (by omega)`. Establish `h4 : ‖g τ‖ ^ 2 ≤ C₀ * |y| ^ k.natAbs`. Combine the equalities or inequalities in the displayed calculation. Establish `h5 : ‖g τ‖ ≤ M` using `by nlinarith [sq_nonneg (‖g τ‖ - 1), norm_nonneg (g τ)]`.

Establish `h3 : 1 ≤ Real.exp (c * |y|) * Real.exp (-c * τ.im)`. Rewrite using `[← Real.exp_add]`. Apply `Real.one_le_exp` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
theorem cuspForm_norm_le_exp_of_one_le_im (G : Subgroup (GL (Fin 2) ℝ)) [G.IsArithmetic] (k : ℤ)
    (g : CuspForm G k) :
    ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖g τ‖ ≤ C * Real.exp (-c * τ.im) := by
  obtain ⟨c, hc, hd⟩ := CuspFormClass.exp_decay_atImInfty' (Γ := G) (k := k) g
  obtain ⟨C₀, hC₀⟩ := CuspFormClass.petersson_bounded_left k G g g
  obtain ⟨D, hD, h⟩ := hd.exists_pos
  rw [Asymptotics.IsBigOWith, atImInfty, eventually_comap, eventually_atTop] at h
  obtain ⟨y, hy⟩ := h
  have hC₀0 : 0 ≤ C₀ := le_trans (norm_nonneg _) (hC₀ UpperHalfPlane.I)
  set M : ℝ := 1 + C₀ * |y| ^ k.natAbs with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨max D (M * Real.exp (c * |y|)), c, hc, fun τ hτ => ?_⟩
  rcases le_total y τ.im with h1 | h1
  · have h2 := hy _ h1 τ rfl
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at h2
    exact h2.trans (by gcongr; exact le_max_left _ _)
  · have hy' : τ.im ≤ |y| := h1.trans (le_abs_self y)
    have hp : ‖g τ‖ ^ 2 * τ.im ^ k ≤ C₀ := by
      have := hC₀ τ
      simp only [UpperHalfPlane.petersson, norm_mul, Complex.norm_conj, norm_zpow,
        Complex.norm_real, Real.norm_of_nonneg τ.im_pos.le] at this
      calc _ = ‖g τ‖ * ‖g τ‖ * τ.im ^ k := by ring
        _ ≤ C₀ := this
    have hpos := τ.im_pos
    have hk : 1 ≤ τ.im ^ k * τ.im ^ k.natAbs := by
      rw [← zpow_natCast, ← zpow_add₀ hpos.ne']
      exact one_le_zpow₀ hτ (by omega)
    have h4 : ‖g τ‖ ^ 2 ≤ C₀ * |y| ^ k.natAbs :=
      calc ‖g τ‖ ^ 2 ≤ ‖g τ‖ ^ 2 * (τ.im ^ k * τ.im ^ k.natAbs) :=
            le_mul_of_one_le_right (by positivity) hk
        _ = ‖g τ‖ ^ 2 * τ.im ^ k * τ.im ^ k.natAbs := by ring
        _ ≤ C₀ * |y| ^ k.natAbs := by gcongr
    have h5 : ‖g τ‖ ≤ M := by nlinarith [sq_nonneg (‖g τ‖ - 1), norm_nonneg (g τ)]
    have h3 : 1 ≤ Real.exp (c * |y|) * Real.exp (-c * τ.im) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    calc ‖g τ‖ ≤ M := h5
      _ ≤ M * (Real.exp (c * |y|) * Real.exp (-c * τ.im)) := le_mul_of_one_le_right hM0 h3
      _ = M * Real.exp (c * |y|) * Real.exp (-c * τ.im) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

/- English proof (translation)
Introduce `Γ k hΓ f σ`. Establish `: ((ConjAct.toConjAct (σ : GL (Fin 2) ℝ)⁻¹) • (Γ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic`. Simplify using `[(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL] using! Subgroup.IsArithmetic.conj (Γ : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ σ)⁻¹`. Conclude with `⟨(CuspForm.translate f (σ : GL (Fin 2) ℝ)).holo', cuspForm_norm_le_exp_of_one_le_im _ k (CuspForm.translate f (σ : GL (Fin 2) ℝ))⟩`.
-/
theorem cuspForm_slash_holo_decay : ∀ (Γ : Subgroup SL(2, ℤ)) (k : ℤ), Γ.FiniteIndex →
    ∀ (f : CuspForm Γ k) (σ : SL(2, ℤ)), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[k] σ) ∧
      ∃ C c : ℝ, 0 < c ∧ ∀ τ : ℍ, 1 ≤ τ.im → ‖(⇑f ∣[k] σ) τ‖ ≤ C * Real.exp (-c * τ.im) := by
  intro Γ k hΓ f σ
  have : ((ConjAct.toConjAct (σ : GL (Fin 2) ℝ)⁻¹) • (Γ : Subgroup (GL (Fin 2) ℝ))).IsArithmetic := by
    simpa [(show Rat.castHom ℝ = algebraMap ℚ ℝ by rfl), map_inv, map_mapGL]
      using! Subgroup.IsArithmetic.conj (Γ : Subgroup (GL (Fin 2) ℝ)) (mapGL ℚ σ)⁻¹
  exact ⟨(CuspForm.translate f (σ : GL (Fin 2) ℝ)).holo',
    cuspForm_norm_le_exp_of_one_le_im _ k (CuspForm.translate f (σ : GL (Fin 2) ℝ))⟩

end GlobalTheory.HeckeFamilyMatrices
