import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChLApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

namespace GlobalTheory.PartRed

/- English proof (translation)
Introduce `k _ _ _ _ ψ hψ R Q _ _ f z Φ hΦ`. Take `⟨h1, h2⟩` from `hΦ`. Establish `hexp : ∀ x : Matrix R Q k, f x = ∑ i, ∑ j, x i j * f (Matrix.single i j 1)`. Introduce `x`. Use `conv_lhs => rw [Matrix.matrix_eq_sum_single x]`.

Simplify using `only [map_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_eq_mul, ← LinearMap.map_smul, Matrix.smul_single, smul_eq_mul, mul_one]`. Establish `hf : Continuous f`. Establish `: (f : Matrix R Q k → k) = fun x => ∑ i, ∑ j, x i j * f (Matrix.single i j 1)` using `funext hexp`.

Rewrite using `[this]`. Conclude with `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => (continuous_id.matrix_elem i j).mul continuous_const`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `((OpenKernel.isLocallyConstant_coe_addChar ψ hψ).comp_continuous (hf.add continuous_const)).mul h1`. Conclude with `h2.mul_left`.
-/
theorem sb_mul_addChar_linear : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (R Q : Type) [Fintype R] [Fintype Q] (f : Matrix R Q k →ₗ[k] k) (z : k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => (ψ (f x + z) : ℂ) * Φ x) ∈ SB (Matrix R Q k) := by
  intro k _ _ _ _ ψ hψ R Q _ _ f z Φ hΦ
  classical
  obtain ⟨h1, h2⟩ := hΦ
  have hexp : ∀ x : Matrix R Q k, f x = ∑ i, ∑ j, x i j * f (Matrix.single i j 1) := by
    intro x
    conv_lhs => rw [Matrix.matrix_eq_sum_single x]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← LinearMap.map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have hf : Continuous f := by
    have : (f : Matrix R Q k → k) = fun x => ∑ i, ∑ j, x i j * f (Matrix.single i j 1) := funext hexp
    rw [this]
    exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      (continuous_id.matrix_elem i j).mul continuous_const
  refine ⟨?_, ?_⟩
  · exact ((OpenKernel.isLocallyConstant_coe_addChar ψ hψ).comp_continuous
      (hf.add continuous_const)).mul h1
  · exact h2.mul_left

end GlobalTheory.PartRed
