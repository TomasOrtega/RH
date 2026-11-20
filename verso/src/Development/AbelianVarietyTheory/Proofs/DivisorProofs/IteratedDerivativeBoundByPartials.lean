import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthElim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClmSupBound

open GlobalTheory.SliceSchwartz GlobalTheory.SliceOp
open scoped ContDiff

/- English proof (translation)
Introduce `X _ _ _`. Use `set b := Module.finBasis ℝ X`. Set `L : Fin (Module.finrank ℝ X) → ℂ →L[ℝ] X →L[ℝ] ℂ` to `fun i => ContinuousLinearMap.smulRightL ℝ X ℂ (LinearMap.toContinuousLinearMap (b.coord i))`. Use `⟨∑ i, ‖L i‖, Finset.sum_nonneg (fun i _ => norm_nonneg _), ?_⟩` and prove the remaining obligations. Introduce `g hg n z`.

Establish `hsm : ∀ i, ContDiff ℝ ∞ (fun w => fderiv ℝ g w (b i))` using `fun i => (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const`. Establish `hdec : fderiv ℝ g = fun w => ∑ i, (L i ∘ (fun w => fderiv ℝ g w (b i))) w`. Use function extensionality and compare the values at `w`. Apply `ContinuousLinearMap.ext` to reduce the goal to its premises. Introduce `v`.

Establish `hv` using `b.sum_repr v`. Simplify using `[L, ContinuousLinearMap.sum_apply]`. Use `conv_lhs => rw [← hv, map_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[map_smul, Complex.real_smul]`.

Establish `key : iteratedFDeriv ℝ n (fderiv ℝ g) z = ∑ i, iteratedFDeriv ℝ n (⇑(L i) ∘ fun w => fderiv ℝ g w (b i)) z` using `by conv_lhs => rw [hdec]`. Rewrite using `[iteratedFDeriv_sum (fun i _ => ((L i).contDiff.comp (hsm i)).of_le (by exact_mod_cast le_top)), Finset.sum_apply]`. Rewrite using `[← norm_iteratedFDeriv_fderiv, key]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(L i).norm_iteratedFDeriv_comp_left (hsm i).contDiffAt (by exact_mod_cast le_top)`.

Use `_ ≤ ∑ i, (∑ j, ‖L j‖) * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (b i)) z‖ := by gcongr with i`. Conclude with `Finset.single_le_sum (f := fun j => ‖L j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)`. Use `_ = (∑ j, ‖L j‖) * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (b i)) z‖ := by`. Rewrite using `[Finset.mul_sum]`.
-/
theorem GlobalTheory.norm_iteratedFDeriv_succ_le_sum_partial :
    ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X],
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : X → ℂ), ContDiff ℝ ∞ g → ∀ (n : ℕ) (z : X),
      ‖iteratedFDeriv ℝ (n + 1) g z‖ ≤ C * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (Module.finBasis ℝ X i)) z‖ := by
  intro X _ _ _
  set b := Module.finBasis ℝ X
  let L : Fin (Module.finrank ℝ X) → ℂ →L[ℝ] X →L[ℝ] ℂ := fun i =>
    ContinuousLinearMap.smulRightL ℝ X ℂ (LinearMap.toContinuousLinearMap (b.coord i))
  refine ⟨∑ i, ‖L i‖, Finset.sum_nonneg (fun i _ => norm_nonneg _), ?_⟩
  intro g hg n z
  have hsm : ∀ i, ContDiff ℝ ∞ (fun w => fderiv ℝ g w (b i)) := fun i =>
    (hg.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hdec : fderiv ℝ g = fun w => ∑ i, (L i ∘ (fun w => fderiv ℝ g w (b i))) w := by
    funext w
    apply ContinuousLinearMap.ext
    intro v
    have hv := b.sum_repr v
    simp [L, ContinuousLinearMap.sum_apply]
    conv_lhs => rw [← hv, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, Complex.real_smul]
  have key : iteratedFDeriv ℝ n (fderiv ℝ g) z =
      ∑ i, iteratedFDeriv ℝ n (⇑(L i) ∘ fun w => fderiv ℝ g w (b i)) z := by
    conv_lhs => rw [hdec]
    rw [iteratedFDeriv_sum (fun i _ => ((L i).contDiff.comp (hsm i)).of_le (by exact_mod_cast le_top)),
      Finset.sum_apply]
  rw [← norm_iteratedFDeriv_fderiv, key]
  calc ‖∑ i, iteratedFDeriv ℝ n (⇑(L i) ∘ fun w => fderiv ℝ g w (b i)) z‖
      ≤ ∑ i, ‖iteratedFDeriv ℝ n (⇑(L i) ∘ fun w => fderiv ℝ g w (b i)) z‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖L i‖ * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (b i)) z‖ := by
        gcongr with i
        exact (L i).norm_iteratedFDeriv_comp_left (hsm i).contDiffAt (by exact_mod_cast le_top)
    _ ≤ ∑ i, (∑ j, ‖L j‖) * ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (b i)) z‖ := by
        gcongr with i
        exact Finset.single_le_sum (f := fun j => ‖L j‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    _ = (∑ j, ‖L j‖) * ∑ i, ‖iteratedFDeriv ℝ n (fun w => fderiv ℝ g w (b i)) z‖ := by
        rw [Finset.mul_sum]
