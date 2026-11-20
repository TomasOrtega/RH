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
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem log_sqrt_eq_phi {m : ℕ} (w : Fin m → ℂ) : Real.log √(∑ i, ‖w i‖ ^ 2) = phi w := by
  have h : (∑ i, ‖w i‖ ^ 2) = sqSum w := rfl
  rw [h, Real.log_sqrt (sqSum_nonneg w), phi]
  ring

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem sqSum_ne_zero {m : ℕ} {w : Fin m → ℂ} (hw : w ≠ 0) : sqSum w ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  refine (lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hi) 2) ?_).ne'
  exact Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

end SheetLogNormDensity

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
