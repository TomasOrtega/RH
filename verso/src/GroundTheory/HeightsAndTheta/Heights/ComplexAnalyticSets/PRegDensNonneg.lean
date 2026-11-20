import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntPos
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGradDensSheetBound
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix ComplexSets
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open scoped ComplexOrder

noncomputable section

namespace RegularizedDensityNonneg

/- English proof (translation)
Simplify using `only [phi, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem half_log_eq_phi (a : ℂ) {ε : ℝ} (hε : 0 ≤ ε) :
    Real.log (‖a‖ ^ 2 + ε) / 2 = phi (![a, ((√ε : ℝ) : ℂ)] : Fin 2 → ℂ) := by
  simp only [phi, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε]
  ring

end RegularizedDensityNonneg

/- English proof (translation)
Introduce `n d J A u ε x s hε hs`. Establish `han : AnalyticAt ℂ s (A *ᵥ x)` using `FormIntegralPositivity.analyticAt_sheet hs`. Use `ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) k` and prove the remaining obligations. Simplify using `only [Matrix.cons_val_zero] set y := A *ᵥ x`.

Establish `hh : AnalyticAt ℂ (fun w => linEval u (s w)) y`. Unfold `linEval`. Conclude with `Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 han) j)`. Set `τ : (Fin (d + 1) → ℂ) → (Fin 2 → ℂ)` to `fun w => ![linEval u (s w), ((√ε : ℝ) : ℂ)]`. Establish `hτ : AnalyticAt ℂ τ y`.

Use `analyticAt_pi_iff.2 fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Simplify `hh` using `[τ]`. Simplify `(analyticAt_const : AnalyticAt ℂ (fun _ : Fin (d + 1) → ℂ => ((√ε : ℝ) : ℂ)) y)` using `[τ]`. Establish `hS : sqSum (τ y) ≠ 0`.

Establish `: sqSum (τ y) = ‖linEval u (s y)‖ ^ 2 + ε`. Simplify using `only [τ, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε.le]`. Rewrite using `[this]`. Check the signs of the components of the expression. Establish `hφ : ContDiffAt ℝ 2 phi (τ y)` using `contDiffAt_phi hS`.

Establish `hfun : logReg u ε ∘ s = phi ∘ τ`. Use function extensionality and compare the values at `w`. Conclude with `RegularizedDensityNonneg.half_log_eq_phi _ hε.le`. Rewrite using `[hfun]`. Use `ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_` and prove the remaining obligations.

Rewrite using `[ReciprocityTheory.AnForm.levi_comp v hτ hφ]`. Conclude with `GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _`. Simplify using `only [Matrix.cons_val_succ]`. Establish `hE : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s (A *ᵥ x))` using `((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt`. Establish `e : (euclPot : (Fin n → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i)`.

Use function extensionality and compare the values at `w`. Simplify using `[euclPot, Complex.normSq_eq_norm_sq]`. Rewrite using `[ReciprocityTheory.AnForm.A.hessC_comp _ _ _ han hE, e, ReciprocityTheory.AnForm.A.hessC_sum_normSq]`. Conclude with `GradDensSheetBound.posSemidef_transpose_mul_mul_conj _ PosSemidef.one`.
-/
theorem RegDensNonneg.proof : RegDensNonneg.Statement := by
  intro n d J A u ε x s hε hs
  have han : AnalyticAt ℂ s (A *ᵥ x) := FormIntegralPositivity.analyticAt_sheet hs
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Matrix.cons_val_zero]
    set y := A *ᵥ x
    have hh : AnalyticAt ℂ (fun w => linEval u (s w)) y := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 han) j)
    let τ : (Fin (d + 1) → ℂ) → (Fin 2 → ℂ) := fun w => ![linEval u (s w), ((√ε : ℝ) : ℂ)]
    have hτ : AnalyticAt ℂ τ y := by
      refine analyticAt_pi_iff.2 fun i => ?_
      fin_cases i
      · simpa [τ] using hh
      · simpa [τ] using (analyticAt_const : AnalyticAt ℂ (fun _ : Fin (d + 1) → ℂ => ((√ε : ℝ) : ℂ)) y)
    have hS : sqSum (τ y) ≠ 0 := by
      have : sqSum (τ y) = ‖linEval u (s y)‖ ^ 2 + ε := by
        simp only [τ, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε.le]
      rw [this]
      positivity
    have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
    have hfun : logReg u ε ∘ s = phi ∘ τ := by
      funext w
      exact RegularizedDensityNonneg.half_log_eq_phi _ hε.le
    rw [hfun]
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  · simp only [Matrix.cons_val_succ]
    have hE : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s (A *ᵥ x)) :=
      ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    have e : (euclPot : (Fin n → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i) := by
      funext w; simp [euclPot, Complex.normSq_eq_norm_sq]
    rw [ReciprocityTheory.AnForm.A.hessC_comp _ _ _ han hE, e, ReciprocityTheory.AnForm.A.hessC_sum_normSq]
    exact GradDensSheetBound.posSemidef_transpose_mul_mul_conj _ PosSemidef.one

end

end GroundTheory.Heights₂.Heights
