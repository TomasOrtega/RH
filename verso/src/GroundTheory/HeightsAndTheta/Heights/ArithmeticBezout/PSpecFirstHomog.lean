import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Take `⟨i, j⟩` from `ij`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Establish `h0 : (fun i : Fin k => groupWeight (k + 1) n ((0 : Fin (k + 1)), j) i.succ) = 0`. Use function extensionality and compare the values at `i`.

Simplify using `[groupWeight, Fin.succ_ne_zero i]`. Rewrite using `[h0]`. Simplify `isWeightedHomogeneous_C (groupWeight k n) (u j)` using `[specFirstVar]`. Consider the case `succ i'`. Establish `h1 : (fun i : Fin k => groupWeight (k + 1) n (i'.succ, j) i.succ) = groupWeight k n (i', j)`.

Use function extensionality and compare the values at `i`. Simplify using `[groupWeight, Pi.single_apply]`. Rewrite using `[h1]`. Simplify `isWeightedHomogeneous_X ℂ (groupWeight k n) (i', j)` using `[specFirstVar]`.
-/
theorem specFirstVar_isWeightedHomogeneous {k n : ℕ} (u : Fin n → ℂ) (ij : Fin (k + 1) × Fin n) :
    IsWeightedHomogeneous (groupWeight k n) (specFirstVar u ij)
      (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
  obtain ⟨i, j⟩ := ij
  induction i using Fin.cases with
  | zero =>
    have h0 : (fun i : Fin k => groupWeight (k + 1) n ((0 : Fin (k + 1)), j) i.succ) = 0 := by
      funext i
      simp [groupWeight, Fin.succ_ne_zero i]
    rw [h0]
    simpa [specFirstVar] using isWeightedHomogeneous_C (groupWeight k n) (u j)
  | succ i' =>
    have h1 : (fun i : Fin k => groupWeight (k + 1) n (i'.succ, j) i.succ) = groupWeight k n (i', j) := by
      funext i
      simp [groupWeight, Pi.single_apply]
    rw [h1]
    simpa [specFirstVar] using isWeightedHomogeneous_X ℂ (groupWeight k n) (i', j)

/- English proof (translation)
Introduce `n k δ f u hf`. Unfold `IsMultiHomog specFirst`. Rewrite using `[f.as_sum, map_sum]`. Use `IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_` and prove the remaining obligations. Rewrite using `[bind₁_monomial]`.

Establish `hdeg : (fun _ : Fin k => δ) = ∑ ij ∈ d.support, d ij • (fun i : Fin k => groupWeight (k + 1) n ij i.succ)`. Establish `hw` using `hf (mem_support_iff.mp hd)`. Use function extensionality and compare the values at `i`. Use `congrFun hw i.succ` as an intermediate fact. Rewrite `this` using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]`.

Rewrite using `[Finset.sum_apply, ← this]`. Both sides reduce to the same expression. Rewrite using `[hdeg]`. Use `IsWeightedHomogeneous.C_mul ?_ _` and prove the remaining obligations. Use `IsWeightedHomogeneous.prod _ _ _ fun ij _ => ?_` and prove the remaining obligations.

Conclude with `(specFirstVar_isWeightedHomogeneous u ij).pow _`.
-/
theorem SpecFirstHomog.proof : SpecFirstHomog.Statement := by
  intro n k δ f u hf
  unfold IsMultiHomog specFirst
  rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [bind₁_monomial]
  have hdeg : (fun _ : Fin k => δ) =
      ∑ ij ∈ d.support, d ij • (fun i : Fin k => groupWeight (k + 1) n ij i.succ) := by
    have hw := hf (mem_support_iff.mp hd)
    funext i
    have := congrFun hw i.succ
    rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply] at this
    rw [Finset.sum_apply, ← this]
    rfl
  rw [hdeg]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun ij _ => ?_
  exact (specFirstVar_isWeightedHomogeneous u ij).pow _

end GroundTheory.Heights₂.Heights
