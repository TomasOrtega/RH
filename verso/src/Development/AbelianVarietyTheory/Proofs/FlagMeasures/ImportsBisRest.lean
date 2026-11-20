import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces

open Finset

namespace GlobalTheory.HermitianFormFacts

/- English proof (translation)
Introduce `ι _ n w`. Use `set S : ℝ := ∑ v : ι, ∑ i, ‖w v i‖ ^ 2 with hS`. Establish `hprod : ∏ v : ι, GlobalTheory.GaussMean.gauss (w v) = Real.exp (-S)`. Unfold `GlobalTheory.GaussMean.gauss`. Rewrite using `[← Real.exp_sum, hS, ← Finset.sum_neg_distrib]`.

Rewrite using `[hprod, Real.exp_le_exp, neg_le_neg_iff]`. Establish `hS0 : 0 ≤ S` using `by positivity`. Establish `hle : ‖w‖ ≤ Real.sqrt S`. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_` and prove the remaining obligations. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_` and prove the remaining obligations.

Apply `Real.le_sqrt_of_sq_le` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem main : ∀ {ι : Type} [inst : Fintype ι] {n : ℕ} (w : ι → Fin n → ℂ),
    ∏ v : ι, GlobalTheory.GaussMean.gauss (w v) ≤ Real.exp (-‖w‖ ^ (2 : ℕ)) := by
  intro ι _ n w
  set S : ℝ := ∑ v : ι, ∑ i, ‖w v i‖ ^ 2 with hS
  have hprod : ∏ v : ι, GlobalTheory.GaussMean.gauss (w v) = Real.exp (-S) := by
    unfold GlobalTheory.GaussMean.gauss
    rw [← Real.exp_sum, hS, ← Finset.sum_neg_distrib]
  rw [hprod, Real.exp_le_exp, neg_le_neg_iff]
  have hS0 : 0 ≤ S := by positivity
  have hle : ‖w‖ ≤ Real.sqrt S := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun v => ?_
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    calc ‖w v i‖ ^ 2 ≤ ∑ j, ‖w v j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖w v j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
      _ ≤ S := Finset.single_le_sum (f := fun u => ∑ j, ‖w u j‖ ^ 2) (fun u _ => by positivity) (Finset.mem_univ v)
  calc ‖w‖ ^ 2 ≤ Real.sqrt S ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = S := Real.sq_sqrt hS0

end GlobalTheory.HermitianFormFacts
