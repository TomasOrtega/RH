import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStabEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAndHasSumKAvg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinCuspApprox

open MeasureTheory Matrix Formalism.REAL GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate

/- English proof (translation)
Introduce `D θ hθ N τ e he a`. Use `set P := N.M.fr τ with hPdef`. Establish `hU : ∀ k : KG (N.M.ε τ), P⁻¹ * toMK k * P ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)` using `fun k => GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k`. Establish `hκ : Continuous fun k : KG (N.M.ε τ) => P⁻¹ * toMK k * P` using `(continuous_const.matrix_mul (GlobalTheory.TypeSum.continuous_toMK _)).matrix_mul continuous_const`. Establish `hA : Continuous fun k : KG (N.M.ε τ) => atTau θ N.V τ (P⁻¹ * toMK k * P)` using `(continuousOn_atTau hθ N.V τ).comp_continuous hκ hU`.

Take `⟨H, hH⟩` from `isCompact_univ.exists_bound_of_continuousOn ((continuous_height N.V).comp hA).continuousOn`. Establish `hHk : ∀ k, height N.V (atTau θ N.V τ (P⁻¹ * toMK k * P)) ≤ |H|` using `fun k => by`. Establish `h` using `hH k (Set.mem_univ k)`. Simplify using `only [Function.comp_apply, Real.norm_eq_abs] at h`. Conclude with `(le_abs_self _).trans (h.trans (le_abs_self _))`.

Establish `hne : Continuous fun k => ‖e k‖` using `he.norm`. Use `⟨(∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * |H| ^ a, mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (pow_nonneg (abs_nonneg _) _), fun f B hf g => ?_⟩` and prove the remaining obligations. Establish `hq` using `quotHeight_pos N.V g`. Establish `hqa : 0 < quotHeight N.V g ^ a` using `pow_pos hq a`. Establish `hpt : ∀ k, ‖e k * f (g * atTau θ N.V τ (P⁻¹ * toMK k * P))‖ ≤ ‖e k‖ * (B * |H| ^ a / quotHeight N.V g ^ a)`.

Introduce `k`. Use `set A := atTau θ N.V τ (P⁻¹ * toMK k * P)`. Establish `h1 : quotHeight N.V g ≤ quotHeight N.V (g * A) * |H|`. Establish `h` using `quotHeight_mul_le N.V (g * A) A⁻¹`. Rewrite `h` using `[mul_inv_cancel_right, height_inv]`.

Conclude with `h.trans (mul_le_mul_of_nonneg_left (hHk k) (quotHeight_pos N.V _).le)`. Establish `h2 : quotHeight N.V g ^ a ≤ quotHeight N.V (g * A) ^ a * |H| ^ a`. Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ hq.le h1 a`. Establish `h3 : ‖f (g * A)‖ * quotHeight N.V g ^ a ≤ B * |H| ^ a`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul]`. Use `mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hqa]`. Conclude with `h3`.

Establish `hint : ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ ≤ ∫ k, ‖e k‖ * (B * |H| ^ a / quotHeight N.V g ^ a) ∂(muK (N.M.ε τ))` using `norm_integral_le_of_norm_le (GlobalTheory.ExpansionAverage.integrable_K (hne.mul continuous_const)) (Filter.Eventually.of_forall hpt)`. Rewrite `hint` using `[integral_mul_const]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem avgN_weighted_bound : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau)
    (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ a : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : GA D N.V → ℂ) (B : ℝ), (∀ g, ‖f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ B) →
        ∀ g, ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ C * B := by
  intro D θ hθ N τ e he a
  set P := N.M.fr τ with hPdef
  have hU : ∀ k : KG (N.M.ε τ), P⁻¹ * toMK k * P ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := fun k =>
    GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k
  have hκ : Continuous fun k : KG (N.M.ε τ) => P⁻¹ * toMK k * P :=
    (continuous_const.matrix_mul (GlobalTheory.TypeSum.continuous_toMK _)).matrix_mul continuous_const
  have hA : Continuous fun k : KG (N.M.ε τ) => atTau θ N.V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ N.V τ).comp_continuous hκ hU
  obtain ⟨H, hH⟩ := isCompact_univ.exists_bound_of_continuousOn ((continuous_height N.V).comp hA).continuousOn
  have hHk : ∀ k, height N.V (atTau θ N.V τ (P⁻¹ * toMK k * P)) ≤ |H| := fun k => by
    have h := hH k (Set.mem_univ k)
    simp only [Function.comp_apply, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (le_abs_self _))
  have hne : Continuous fun k => ‖e k‖ := he.norm
  refine ⟨(∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * |H| ^ a,
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (pow_nonneg (abs_nonneg _) _), fun f B hf g => ?_⟩
  have hq := quotHeight_pos N.V g
  have hqa : 0 < quotHeight N.V g ^ a := pow_pos hq a
  have hpt : ∀ k, ‖e k * f (g * atTau θ N.V τ (P⁻¹ * toMK k * P))‖ ≤
      ‖e k‖ * (B * |H| ^ a / quotHeight N.V g ^ a) := by
    intro k
    set A := atTau θ N.V τ (P⁻¹ * toMK k * P)
    have h1 : quotHeight N.V g ≤ quotHeight N.V (g * A) * |H| := by
      have h := quotHeight_mul_le N.V (g * A) A⁻¹
      rw [mul_inv_cancel_right, height_inv] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hHk k) (quotHeight_pos N.V _).le)
    have h2 : quotHeight N.V g ^ a ≤ quotHeight N.V (g * A) ^ a * |H| ^ a := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hq.le h1 a
    have h3 : ‖f (g * A)‖ * quotHeight N.V g ^ a ≤ B * |H| ^ a :=
      calc ‖f (g * A)‖ * quotHeight N.V g ^ a ≤ ‖f (g * A)‖ * (quotHeight N.V (g * A) ^ a * |H| ^ a) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = (‖f (g * A)‖ * quotHeight N.V (g * A) ^ a) * |H| ^ a := by ring
        _ ≤ B * |H| ^ a := mul_le_mul_of_nonneg_right (hf _) (by positivity)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [le_div_iff₀ hqa]; exact h3
  have hint : ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ ≤
      ∫ k, ‖e k‖ * (B * |H| ^ a / quotHeight N.V g ^ a) ∂(muK (N.M.ε τ)) :=
    norm_integral_le_of_norm_le (GlobalTheory.ExpansionAverage.integrable_K (hne.mul continuous_const))
      (Filter.Eventually.of_forall hpt)
  rw [integral_mul_const] at hint
  calc ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * quotHeight N.V g ^ a
      ≤ ((∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * (B * |H| ^ a / quotHeight N.V g ^ a)) * quotHeight N.V g ^ a :=
        mul_le_mul_of_nonneg_right hint hqa.le
    _ = (∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * |H| ^ a * B := by field_simp

end GlobalTheory.KFinCuspApprox

end
