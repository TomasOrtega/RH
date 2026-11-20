import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero

open IsDedekindDomain NumberField
open scoped Classical

/- English proof (translation)
Introduce `E _ _ ι _ b j`. Use `haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b`. Use `set C := ‖(b.equivFunL : E →L[ℝ] (ι → ℝ))‖ with hC`. Establish `hC0 : 0 ≤ C` using `norm_nonneg _`. Establish `hcoord : ∀ (x : E) (c : ι), ‖b.repr x c‖ ≤ C * ‖x‖`.

Introduce `x c`. Establish `h1 : b.repr x c = (b.equivFunL : E →L[ℝ] (ι → ℝ)) x c` using `rfl`. Rewrite using `[h1]`. Conclude with `(norm_le_pi_norm _ c).trans ((b.equivFunL : E →L[ℝ] (ι → ℝ)).le_opNorm x)`. Use `⟨C ^ j, pow_nonneg hC0 _, fun M => ?_⟩` and prove the remaining obligations.

Apply `ContinuousMultilinearMap.opNorm_le_bound` to reduce the goal to its premises. Conclude with `mul_nonneg (pow_nonneg hC0 _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)`. Introduce `v`. Establish `hv : v = fun r => ∑ c, b.repr (v r) c • b c` using `funext fun r => (b.sum_repr (v r)).symm`. Establish `key : M v = ∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))` using `by conv_lhs => rw [hv]`.

Rewrite using `[M.map_sum]`. Use `Finset.sum_congr rfl fun cs _ => ?_` and prove the remaining obligations. Conclude with `M.map_smul_univ (fun r => b.repr (v r) (cs r)) (fun r => b (cs r))`. Rewrite using `[key]`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum fun cs _ => ?_` and prove the remaining obligations. Rewrite using `[norm_smul]`. Use `mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[norm_prod, ← Fin.prod_const, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun r _ => hcoord (v r) (cs r)`.

Use `_ = C ^ j * (∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖) * ∏ r, ‖v r‖ := by`. Rewrite using `[Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun cs _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.continuousMultilinear_norm_le_basis_sum : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] (b : Module.Basis ι ℝ E) (j : ℕ),
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ,
      ‖M‖ ≤ K * ∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖ := by
  intro E _ _ ι _ b j
  haveI : FiniteDimensional ℝ E := Module.Finite.of_basis b
  set C := ‖(b.equivFunL : E →L[ℝ] (ι → ℝ))‖ with hC
  have hC0 : 0 ≤ C := norm_nonneg _
  have hcoord : ∀ (x : E) (c : ι), ‖b.repr x c‖ ≤ C * ‖x‖ := by
    intro x c
    have h1 : b.repr x c = (b.equivFunL : E →L[ℝ] (ι → ℝ)) x c := rfl
    rw [h1]
    exact (norm_le_pi_norm _ c).trans ((b.equivFunL : E →L[ℝ] (ι → ℝ)).le_opNorm x)
  refine ⟨C ^ j, pow_nonneg hC0 _, fun M => ?_⟩
  apply ContinuousMultilinearMap.opNorm_le_bound
  · exact mul_nonneg (pow_nonneg hC0 _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro v
  have hv : v = fun r => ∑ c, b.repr (v r) c • b c := funext fun r => (b.sum_repr (v r)).symm
  have key : M v = ∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r)) := by
    conv_lhs => rw [hv]
    rw [M.map_sum]
    refine Finset.sum_congr rfl fun cs _ => ?_
    exact M.map_smul_univ (fun r => b.repr (v r) (cs r)) (fun r => b (cs r))
  rw [key]
  calc ‖∑ cs : Fin j → ι, (∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))‖
      ≤ ∑ cs : Fin j → ι, ‖(∏ r, b.repr (v r) (cs r)) • M (fun r => b (cs r))‖ := norm_sum_le _ _
    _ ≤ ∑ cs : Fin j → ι, (C ^ j * ∏ r, ‖v r‖) * ‖M (fun r => b (cs r))‖ := by
      refine Finset.sum_le_sum fun cs _ => ?_
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [norm_prod, ← Fin.prod_const, ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun r _ => hcoord (v r) (cs r)
    _ = C ^ j * (∑ cs : Fin j → ι, ‖M (fun r => b (cs r))‖) * ∏ r, ‖v r‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun cs _ => ?_
      ring
