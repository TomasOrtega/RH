import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.FactorApply
open scoped TensorProduct
open UpperTheory.Lit.HoweDuality

/- English proof (translation)
Introduce `ι _ _ M₀ _ _ M _ _ i`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.eq_top_iff']`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `add a b ha hb => exact Submodule.add_mem _ ha hb`. Consider the case `tmul x₀ w`. Proceed by induction on `w using PiTensorProduct.induction_on with`. Consider the case `smul_tprod c y`.

Rewrite using `[TensorProduct.tmul_smul]`. Use `Submodule.smul_mem _ c ?_` and prove the remaining obligations. Use `Submodule.mem_iSup_of_mem (x₀, y) ⟨y i, ?_⟩` and prove the remaining obligations. Rewrite using `[position_apply]`. Simplify using `only [Function.update_eq_self]`.

Consider the case `add a b ha hb`. Rewrite using `[TensorProduct.tmul_add]`. Conclude with `Submodule.add_mem _ ha hb`. Introduce `g r x`. Rewrite using `[position_apply, position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]`.

Use `congr 2`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Function.update_of_ne h]`.
-/
theorem UpperTheory.Lit.HoweDuality.slotFacts :
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {M₀ : Type} [AddCommGroup M₀] [Module ℂ M₀] {M : ι → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)] (i : ι), (⨆ r : M₀ × (∀ j, M j), LinearMap.range (intersection_update_fsHerm_neg_one i r)) = ⊤ ∧ ∀ (g : Module.End ℂ (M i)) (r : M₀ × (∀ j, M j)) (x : M i), factorOp i g (intersection_update_fsHerm_neg_one i r x) = intersection_update_fsHerm_neg_one i r (g x) := by
  intro ι _ _ M₀ _ _ M _ _ i
  refine ⟨?_, ?_⟩
  · rw [Submodule.eq_top_iff']
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | add a b ha hb => exact Submodule.add_mem _ ha hb
    | tmul x₀ w =>
      induction w using PiTensorProduct.induction_on with
      | smul_tprod c y =>
        rw [TensorProduct.tmul_smul]
        refine Submodule.smul_mem _ c ?_
        refine Submodule.mem_iSup_of_mem (x₀, y) ⟨y i, ?_⟩
        rw [position_apply]
        simp only [Function.update_eq_self]
      | add a b ha hb =>
        rw [TensorProduct.tmul_add]
        exact Submodule.add_mem _ ha hb
  · intro g r x
    rw [position_apply, position_apply, factorOp, TensorProduct.map_tmul, PiTensorProduct.map_tprod]
    congr 2
    funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Function.update_of_ne h]
