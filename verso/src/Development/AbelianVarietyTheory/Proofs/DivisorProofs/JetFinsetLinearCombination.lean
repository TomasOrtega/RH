import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

/- English proof (translation)
Introduce `ι _ a b cD α R c F hF m`. Establish `key : ∀ (k : ℕ) (v : Fin k → VCx ι a b), iteratedFDeriv ℂ k (fun w => ∑ i ∈ R, c i * F i w) 0 v = ∑ i ∈ R, c i * iteratedFDeriv ℂ k (F i) 0 v`. Introduce `k v`. Establish `hC : ∀ i ∈ R, ContDiff ℂ k (F i)` using `fun i hi => GlobalTheory.SCV.contDiff_of_differentiable (hF i hi) _`. Establish `h1` using `iteratedFDeriv_sum (𝕜 := ℂ) (f := fun i w => c i * F i w) (u := R) (i := k) (fun i hi => contDiff_const.mul (hC i hi))`.

Rewrite using `[h1, Finset.sum_apply, ContinuousMultilinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `h2` using `iteratedFDeriv_const_smul_apply' (𝕜 := ℂ) (a := c i) (f := F i) (i := k) (x := 0) (hC i hi).contDiffAt`. Simplify using `only [smul_eq_mul] at h2`. Rewrite using `[h2]`.

Simplify using the standard rewrite rules. Unfold `jetC derivAt0`. Rewrite using `[key, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.ColNorms.jetC_sum_mul : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (cD : ι → ℂ) (α : Type) (R : Finset α) (c : α → ℂ) (F : α → VCx ι a b → ℂ), (∀ x ∈ R, Differentiable ℂ (F x)) → ∀ m, jetC cD (fun z => ∑ x ∈ R, c x * F x z) m = ∑ x ∈ R, c x * jetC cD (F x) m := by
  intro ι _ a b cD α R c F hF m
  have key : ∀ (k : ℕ) (v : Fin k → VCx ι a b),
      iteratedFDeriv ℂ k (fun w => ∑ i ∈ R, c i * F i w) 0 v =
        ∑ i ∈ R, c i * iteratedFDeriv ℂ k (F i) 0 v := by
    intro k v
    have hC : ∀ i ∈ R, ContDiff ℂ k (F i) := fun i hi =>
      GlobalTheory.SCV.contDiff_of_differentiable (hF i hi) _
    have h1 := iteratedFDeriv_sum (𝕜 := ℂ) (f := fun i w => c i * F i w) (u := R) (i := k)
      (fun i hi => contDiff_const.mul (hC i hi))
    rw [h1, Finset.sum_apply, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    have h2 := iteratedFDeriv_const_smul_apply' (𝕜 := ℂ) (a := c i) (f := F i) (i := k) (x := 0)
      (hC i hi).contDiffAt
    simp only [smul_eq_mul] at h2
    rw [h2]
    simp
  unfold jetC derivAt0
  rw [key, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring
