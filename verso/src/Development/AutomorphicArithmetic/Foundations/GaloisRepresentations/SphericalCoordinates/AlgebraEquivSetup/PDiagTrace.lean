import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Introduce `I _ a M hM`. Establish `hdec : M = ∑ k, (LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k)`. Use `LinearMap.ext fun z => funext fun j => ?_` and prove the remaining obligations. Simplify using `[hM, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]`. Establish `hk : ∀ k : I, LinearMap.trace ℝ (I → ℂ) ((LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k)) = 2 * (a k).re`.

Introduce `k`. Rewrite using `[LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.proj_comp_single_same, LinearMap.comp_id, ← Algebra.trace_complex_apply, Algebra.trace_apply]`. Rewrite using `[hdec, map_sum, Finset.sum_congr rfl (fun k _ => hk k), Complex.re_sum, Finset.mul_sum]`.
-/
theorem UpperTheory.Gal.W2.Seed.pDiagTrace :
    DiagTrace := by
  intro I _ a M hM
  classical
  have hdec : M = ∑ k, (LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ
      ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k) := by
    refine LinearMap.ext fun z => funext fun j => ?_
    simp [hM, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]
  have hk : ∀ k : I, LinearMap.trace ℝ (I → ℂ) ((LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ
      ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k)) = 2 * (a k).re := by
    intro k
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.proj_comp_single_same,
      LinearMap.comp_id, ← Algebra.trace_complex_apply, Algebra.trace_apply]
  rw [hdec, map_sum, Finset.sum_congr rfl (fun k _ => hk k), Complex.re_sum, Finset.mul_sum]
