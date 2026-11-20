import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetLogNormDens
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntPos
import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
import ReciprocityTheory.AnalyticForms.PotentialTheory.HessCIsHermitian
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix ComplexSets
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi

noncomputable section

namespace SheetLogNormDensity

/- English proof (translation)
Establish `h : (∑ i, ‖w i‖ ^ 2) = sqSum w` using `rfl`. Rewrite using `[h, Real.log_sqrt (sqSum_nonneg w), phi]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_sqrt_eq_phi {m : ℕ} (w : Fin m → ℂ) : Real.log √(∑ i, ‖w i‖ ^ 2) = phi w := by
  have h : (∑ i, ‖w i‖ ^ 2) = sqSum w := rfl
  rw [h, Real.log_sqrt (sqSum_nonneg w), phi]
  ring

/- English proof (translation)
Take `⟨i, hi⟩` from `Function.ne_iff.mp hw`. Use `(lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2) ?_).ne'` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)`.
-/
theorem sqSum_ne_zero {m : ℕ} {w : Fin m → ℂ} (hw : w ≠ 0) : sqSum w ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2) ?_).ne'
  exact Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

end SheetLogNormDensity

/- English proof (translation)
Introduce `n d m J A x s T hs hT`. Establish `hsx : s (A *ᵥ x) = x`. Take `⟨_, _, _, _, h, _⟩` from `hs`. Conclude with `h`. Establish `han` using `FormIntegralPositivity.analyticAt_sheet hs`.

Use `ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_` and prove the remaining obligations. Set `L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ)` to `LinearMap.toContinuousLinearMap (Matrix.mulVecLin (T k))`. Establish `hL : ∀ z, L z = T k *ᵥ z` using `fun z => rfl`. Establish `hτ : AnalyticAt ℂ (L ∘ s) (A *ᵥ x)` using `(L.analyticAt _).comp han`. Establish `hS : sqSum ((L ∘ s) (A *ᵥ x)) ≠ 0`.

Rewrite using `[Function.comp_apply, hsx, hL]`. Conclude with `SheetLogNormDensity.sqSum_ne_zero (hT k)`. Establish `hφ : ContDiffAt ℝ 2 phi ((L ∘ s) (A *ᵥ x))` using `contDiffAt_phi hS`. Establish `hfun : (fun z => Real.log √(∑ i, ‖(T k *ᵥ z) i‖ ^ 2)) ∘ s = phi ∘ (L ∘ s)`. Use function extensionality and compare the values at `y`.

Simplify using `only [Function.comp_apply, hL]`. Conclude with `SheetLogNormDensity.log_sqrt_eq_phi _`. Rewrite using `[hfun]`. Use `ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_` and prove the remaining obligations. Rewrite using `[ReciprocityTheory.AnForm.levi_comp v hτ hφ]`.

Conclude with `GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _`.
-/
theorem SheetLogNormDens.proof : SheetLogNormDens.Statement := by
  intro n d m J A x s T hs hT
  have hsx : s (A *ᵥ x) = x := by
    obtain ⟨_, _, _, _, h, _⟩ := hs
    exact h
  have han := FormIntegralPositivity.analyticAt_sheet hs
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun k => ?_
  let L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin (T k))
  have hL : ∀ z, L z = T k *ᵥ z := fun z => rfl
  have hτ : AnalyticAt ℂ (L ∘ s) (A *ᵥ x) := (L.analyticAt _).comp han
  have hS : sqSum ((L ∘ s) (A *ᵥ x)) ≠ 0 := by
    rw [Function.comp_apply, hsx, hL]
    exact SheetLogNormDensity.sqSum_ne_zero (hT k)
  have hφ : ContDiffAt ℝ 2 phi ((L ∘ s) (A *ᵥ x)) := contDiffAt_phi hS
  have hfun : (fun z => Real.log √(∑ i, ‖(T k *ᵥ z) i‖ ^ 2)) ∘ s = phi ∘ (L ∘ s) := by
    funext y
    simp only [Function.comp_apply, hL]
    exact SheetLogNormDensity.log_sqrt_eq_phi _
  rw [hfun]
  refine ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ (hφ.comp _ hτ.restrictScalars.contDiffAt) fun v => ?_
  rw [ReciprocityTheory.AnForm.levi_comp v hτ hφ]
  exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _

end

end GroundTheory.Heights₂.Heights
