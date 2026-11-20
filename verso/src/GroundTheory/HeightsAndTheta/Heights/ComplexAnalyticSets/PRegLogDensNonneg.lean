import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLogDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegDensNonneg
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntPos
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix ComplexSets
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open scoped ComplexOrder

noncomputable section

namespace RegularizedLogDensityNonneg

/- English proof (translation)
Set `τ : (Fin e → ℂ) → Fin n → ℂ` to `fun w => s w - x`. Establish `hτ : AnalyticAt ℂ τ y` using `han.sub analyticAt_const`. Establish `hS : sqSum (τ y) ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises.

Establish `hj : ∀ j ∈ Finset.univ, ‖(s y - x) j‖ ^ 2 = 0` using `(Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 h0`. Use function extensionality and compare the values at `j`. Use `hj j (Finset.mem_univ j)` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Establish `hφ : ContDiffAt ℝ 2 phi (τ y)` using `contDiffAt_phi hS`.

Establish `hfun : logDistSq x ∘ s = fun w => 2 * (phi ∘ τ) w`. Use function extensionality and compare the values at `w`. Simplify using `only [Function.comp_apply, logDistSq, phi, τ, euclPot, sqSum]`. Expand and normalize the polynomial expressions, which then agree. Establish `hP : (ReciprocityTheory.AnForm.hessC (phi ∘ τ) y).PosSemidef`.

Use `ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.AnForm.levi_comp v hτ hφ]`. Conclude with `GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _`. Rewrite using `[hfun, ReciprocityTheory.AnForm.M.hessC_const_mul']`. Conclude with `hP.smul (by norm_num)`.
-/
theorem hessC_logDistSq_comp_posSemidef {n e : ℕ} (x : Fin n → ℂ) (s : (Fin e → ℂ) → Fin n → ℂ)
    (y : Fin e → ℂ) (han : AnalyticAt ℂ s y) (hne : s y ≠ x) :
    (ReciprocityTheory.AnForm.hessC (logDistSq x ∘ s) y).PosSemidef := by
  let τ : (Fin e → ℂ) → Fin n → ℂ := fun w => s w - x
  have hτ : AnalyticAt ℂ τ y := han.sub analyticAt_const
  have hS : sqSum (τ y) ≠ 0 := by
    intro h0
    apply hne
    have hj : ∀ j ∈ Finset.univ, ‖(s y - x) j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 h0
    funext j
    have := hj j (Finset.mem_univ j)
    simpa [sub_eq_zero] using this
  have hφ : ContDiffAt ℝ 2 phi (τ y) := contDiffAt_phi hS
  have hfun : logDistSq x ∘ s = fun w => 2 * (phi ∘ τ) w := by
    funext w
    simp only [Function.comp_apply, logDistSq, phi, τ, euclPot, sqSum]
    ring
  have hP : (ReciprocityTheory.AnForm.hessC (phi ∘ τ) y).PosSemidef := by
    refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
    rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
    exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _
  rw [hfun, ReciprocityTheory.AnForm.M.hessC_const_mul']
  exact hP.smul (by norm_num)

end RegularizedLogDensityNonneg

/- English proof (translation)
Introduce `n d J A u ε x z s hε hzx hs`. Establish `han : AnalyticAt ℂ s (A *ᵥ z)` using `FormIntegralPositivity.analyticAt_sheet hs`. Establish `hsz : s (A *ᵥ z) = z`. Take `⟨U, -, -, -, h, -⟩` from `hs`. Conclude with `h`.

Use `ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) k` and prove the remaining obligations. Simplify using `only [Matrix.cons_val_zero] set y := A *ᵥ z`. Establish `hh : AnalyticAt ℂ (fun w => linEval u (s w)) y`. Unfold `linEval`.

Conclude with `Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 han) j)`. Set `τ : (Fin (d + 1) → ℂ) → (Fin 2 → ℂ)` to `fun w => ![linEval u (s w), ((√ε : ℝ) : ℂ)]`. Establish `hτ : AnalyticAt ℂ τ y`. Use `analyticAt_pi_iff.2 fun i => ?_` and prove the remaining obligations. Use `fin_cases i`.

Simplify `hh` using `[τ]`. Simplify `(analyticAt_const : AnalyticAt ℂ (fun _ : Fin (d + 1) → ℂ => ((√ε : ℝ) : ℂ)) y)` using `[τ]`. Establish `hS : sqSum (τ y) ≠ 0`. Establish `: sqSum (τ y) = ‖linEval u (s y)‖ ^ 2 + ε`. Simplify using `only [τ, sqSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hε.le]`.

Rewrite using `[this]`. Check the signs of the components of the expression. Establish `hφ : ContDiffAt ℝ 2 phi (τ y)` using `contDiffAt_phi hS`. Establish `hfun : logReg u ε ∘ s = phi ∘ τ`. Use function extensionality and compare the values at `w`.

Conclude with `RegularizedDensityNonneg.half_log_eq_phi _ hε.le`. Rewrite using `[hfun]`. Use `ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.AnForm.levi_comp v hτ hφ]`. Conclude with `GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _`.

Simplify using `only [Matrix.cons_val_succ]`. Conclude with `RegularizedLogDensityNonneg.hessC_logDistSq_comp_posSemidef x s _ han (hsz.symm ▸ hzx)`.
-/
theorem RegLogDensNonneg.proof : RegLogDensNonneg.Statement := by
  intro n d J A u ε x z s hε hzx hs
  have han : AnalyticAt ℂ s (A *ᵥ z) := FormIntegralPositivity.analyticAt_sheet hs
  have hsz : s (A *ᵥ z) = z := by
    obtain ⟨U, -, -, -, h, -⟩ := hs
    exact h
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  refine Fin.cases ?_ (fun j => ?_) k
  · simp only [Matrix.cons_val_zero]
    set y := A *ᵥ z
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
    exact RegularizedLogDensityNonneg.hessC_logDistSq_comp_posSemidef x s _ han (hsz.symm ▸ hzx)

end

end GroundTheory.Heights₂.Heights
