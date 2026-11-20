import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

variable {n : ℕ}

def dOne (f : V n → ℂ) (v : V n) : Alt n := ∑ a, del f v (coordVec a) • dz a

/- English proof (translation)
Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem delAt_eq_sum_dOne (β : V n → Alt n) (u : V n) :
    delAt β u = ∑ T, dOne (fun x => (bas n).repr (β x) T) u * bas n T := by
  simp only [delAt, coefwise, dOne, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  exact Finset.sum_comm

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem delAt_congr {F G : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] G) : delAt F v = delAt G v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => congrArg _ (Finset.sum_congr rfl fun S _ => ?_)
  have e : del (fun x => (bas n).repr (F x) S) v = del (fun x => (bas n).repr (G x) S) v :=
    del_congr (h.fun_comp fun y => (bas n).repr y S)
  simp only [e]

end GlobalTheory.CxForm.DelForm
