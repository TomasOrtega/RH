import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
open Matrix GlobalTheory.PELU
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)

namespace GlobalTheory.PosOpen

/- English proof (translation)
Simplify using `only [hermForm, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]`. Simplify using `[Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermForm_smul_real {g : ℕ} (N : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (z : Fin g → ℂ) :
    hermForm N ((r : ℂ) • z) ((r : ℂ) • z) = ((r * r : ℝ) : ℂ) * hermForm N z z := by
  simp only [hermForm, star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  simp [Complex.conj_ofReal]
  ring

/- English proof (translation)
Introduce `g M₀ hM`. Establish `cA : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => 1 - C.map star * C` using `continuous_const.sub ((continuous_id.matrix_map continuous_star).matrix_mul continuous_id)`. Establish `cB : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => 1 - C * C.map star` using `continuous_const.sub (continuous_id.matrix_mul (continuous_id.matrix_map continuous_star))`. Establish `dA : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => (1 - C.map star * C).det` using `cA.matrix_det`. Establish `dB : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => (1 - C * C.map star).det` using `cB.matrix_det`.

Establish `dA0 : (1 - (0 : Matrix (Fin g) (Fin g) ℂ).map star * 0).det ≠ 0` using `by simp`. Establish `dB0 : (1 - (0 : Matrix (Fin g) (Fin g) ℂ) * (0 : Matrix (Fin g) (Fin g) ℂ).map star).det ≠ 0` using `by simp`. Establish `e1` using `dA.continuousAt.eventually_ne dA0`. Establish `e2` using `dB.continuousAt.eventually_ne dB0`. Establish `cInv : ContinuousAt (fun C : Matrix (Fin g) (Fin g) ℂ => M₀ * (1 - C.map star * C)⁻¹) 0`.

Establish `h1 : (fun C : Matrix (Fin g) (Fin g) ℂ => M₀ * (1 - C.map star * C)⁻¹) = fun C => M₀ * (((1 - C.map star * C).det)⁻¹ • (1 - C.map star * C).adjugate)`. Use function extensionality and compare the values at `C`. Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv']`. Rewrite using `[h1]`. Use `continuousAt_const.mul (ContinuousAt.smul (dA.continuousAt.inv₀ dA0) cA.matrix_adjugate.continuousAt)` and prove the remaining obligations.

Establish `cH : Continuous fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm p.1 p.2 p.2).re` using `Complex.continuous_re.comp (continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd.star))`. Establish `tube : ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), ∀ y ∈ Metric.sphere (0 : Fin g → ℂ) 1, 0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) y y).re`. Use `(isCompact_sphere (0 : Fin g → ℂ) 1).eventually_forall_of_forall_eventually fun y hy => ?_` and prove the remaining obligations. Establish `cF : ContinuousAt (fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm (M₀ * (1 - p.1.map star * p.1)⁻¹) p.2 p.2).re) (0, y)`. Establish `: ContinuousAt (fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (M₀ * (1 - p.1.map star * p.1)⁻¹, p.2)) (0, y)` using `(ContinuousAt.comp (x := ((0 : Matrix (Fin g) (Fin g) ℂ), y)) (f := (Prod.fst : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ)) cInv continuousAt_fst).prodMk continuousAt_snd`.

Conclude with `ContinuousAt.comp (x := ((0 : Matrix (Fin g) (Fin g) ℂ), y)) (g := fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm p.1 p.2 p.2).re) (f := fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (M₀ * (1 - p.1.map star * p.1)⁻¹, p.2)) cH.continuousAt this`. Establish `hy0 : y ≠ 0` using `by rintro rfl; simp at hy`. Establish `v0 : 0 < (hermForm (M₀ * (1 - (0 : Matrix (Fin g) (Fin g) ℂ).map star * 0)⁻¹) y y).re`. Simplify using `using hM y hy0`. Conclude with `cF.eventually (lt_mem_nhds v0)`.

Use `filter_upwards [e1, e2, tube] with C h1 h2 h3`. Use `⟨h1, h2, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hn : 0 < ‖z‖` using `norm_pos_iff.mpr hz`. Establish `hu : ((‖z‖⁻¹ : ℝ) : ℂ) • z ∈ Metric.sphere (0 : Fin g → ℂ) 1`. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']`.

Use `h3 _ hu` as an intermediate fact. Rewrite `this` using `[hermForm_smul_real, Complex.re_ofReal_mul]`. Conclude with `pos_of_mul_pos_right this (by positivity)`.
-/
theorem posopen : ∀ {g : ℕ} (M₀ : Matrix (Fin g) (Fin g) ℂ), (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm M₀ z z).re) →
    ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), (1 - C.map star * C).det ≠ 0 ∧ (1 - C * C.map star).det ≠ 0 ∧
      ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) z z).re := by
  intro g M₀ hM
  have cA : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => 1 - C.map star * C :=
    continuous_const.sub ((continuous_id.matrix_map continuous_star).matrix_mul continuous_id)
  have cB : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => 1 - C * C.map star :=
    continuous_const.sub (continuous_id.matrix_mul (continuous_id.matrix_map continuous_star))
  have dA : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => (1 - C.map star * C).det := cA.matrix_det
  have dB : Continuous fun C : Matrix (Fin g) (Fin g) ℂ => (1 - C * C.map star).det := cB.matrix_det
  have dA0 : (1 - (0 : Matrix (Fin g) (Fin g) ℂ).map star * 0).det ≠ 0 := by simp
  have dB0 : (1 - (0 : Matrix (Fin g) (Fin g) ℂ) * (0 : Matrix (Fin g) (Fin g) ℂ).map star).det ≠ 0 := by simp
  have e1 := dA.continuousAt.eventually_ne dA0
  have e2 := dB.continuousAt.eventually_ne dB0

  have cInv : ContinuousAt (fun C : Matrix (Fin g) (Fin g) ℂ => M₀ * (1 - C.map star * C)⁻¹) 0 := by
    have h1 : (fun C : Matrix (Fin g) (Fin g) ℂ => M₀ * (1 - C.map star * C)⁻¹) =
        fun C => M₀ * (((1 - C.map star * C).det)⁻¹ • (1 - C.map star * C).adjugate) := by
      funext C
      rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h1]
    refine continuousAt_const.mul (ContinuousAt.smul (dA.continuousAt.inv₀ dA0) cA.matrix_adjugate.continuousAt)
  have cH : Continuous fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm p.1 p.2 p.2).re :=
    Complex.continuous_re.comp (continuous_snd.dotProduct (continuous_fst.matrix_mulVec continuous_snd.star))
  have tube : ∀ᶠ C in nhds (0 : Matrix (Fin g) (Fin g) ℂ), ∀ y ∈ Metric.sphere (0 : Fin g → ℂ) 1,
      0 < (hermForm (M₀ * (1 - C.map star * C)⁻¹) y y).re := by
    refine (isCompact_sphere (0 : Fin g → ℂ) 1).eventually_forall_of_forall_eventually fun y hy => ?_
    have cF : ContinuousAt (fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) =>
        (hermForm (M₀ * (1 - p.1.map star * p.1)⁻¹) p.2 p.2).re) (0, y) := by
      have : ContinuousAt (fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) =>
          (M₀ * (1 - p.1.map star * p.1)⁻¹, p.2)) (0, y) :=
        (ContinuousAt.comp (x := ((0 : Matrix (Fin g) (Fin g) ℂ), y))
          (f := (Prod.fst : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) → Matrix (Fin g) (Fin g) ℂ)) cInv
          continuousAt_fst).prodMk continuousAt_snd
      exact ContinuousAt.comp (x := ((0 : Matrix (Fin g) (Fin g) ℂ), y))
        (g := fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (hermForm p.1 p.2 p.2).re)
        (f := fun p : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => (M₀ * (1 - p.1.map star * p.1)⁻¹, p.2))
        cH.continuousAt this
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy
    have v0 : 0 < (hermForm (M₀ * (1 - (0 : Matrix (Fin g) (Fin g) ℂ).map star * 0)⁻¹) y y).re := by
      simpa using hM y hy0
    exact cF.eventually (lt_mem_nhds v0)
  filter_upwards [e1, e2, tube] with C h1 h2 h3
  refine ⟨h1, h2, fun z hz => ?_⟩
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hu : ((‖z‖⁻¹ : ℝ) : ℂ) • z ∈ Metric.sphere (0 : Fin g → ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have := h3 _ hu
  rw [hermForm_smul_real, Complex.re_ofReal_mul] at this
  exact pos_of_mul_pos_right this (by positivity)

end GlobalTheory.PosOpen
