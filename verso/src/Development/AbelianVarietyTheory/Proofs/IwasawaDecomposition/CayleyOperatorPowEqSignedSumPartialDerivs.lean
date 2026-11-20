import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph
open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

set_option autoImplicit false

namespace GlobalTheory.CayleyBlock

/- English proof (translation)
Simplify using `[dList, List.map_append, List.prod_append]`.
-/
theorem dList_append' {σ : Type} [DecidableEq σ] (l₁ l₂ : List σ) :
    dList (l₁ ++ l₂) = dList l₁ * dList l₂ := by
  simp [dList, List.map_append, List.prod_append]

/- English proof (translation)
Simplify using `[smallList, List.finRange_succ, List.flatMap_cons, List.flatMap_map]`.
-/
theorem smallList_cons' {p q : ℕ} (σ : Equiv.Perm (Fin p)) (τ : Fin q → Equiv.Perm (Fin p)) :
    smallList (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) =
      (List.finRange p).map (fun j => (σ j, j)) ++ smallList τ := by
  simp [smallList, List.finRange_succ, List.flatMap_cons, List.flatMap_map]

/- English proof (translation)
Simplify using `[sgnProd, Fin.prod_univ_succ]`.
-/
theorem sgnProd_cons' {p q : ℕ} (σ : Equiv.Perm (Fin p)) (τ : Fin q → Equiv.Perm (Fin p)) :
    sgnProd (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) =
      (Equiv.Perm.sign σ : ℤ) * sgnProd τ := by
  simp [sgnProd, Fin.prod_univ_succ]

/- English proof (translation)
Simplify using `[cayMono, dList, List.map_map]`. Both sides reduce to the same expression.
-/
theorem cayMono_eq_dList' {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    cayMono p ℂ σ = dList ((List.finRange p).map fun j => (σ j, j)) := by
  simp [cayMono, dList, List.map_map]
  rfl

/- English proof (translation)
Proceed by induction on `q with`. Consider the case `zero => simp [smallList, sgnProd, dList]`. Consider the case `succ q ih`. Rewrite using `[pow_succ', ih, cayOp, Finset.sum_mul_sum, ← (Fin.consEquiv (fun _ => Equiv.Perm (Fin p))).sum_comp, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `_ = sgnProd (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) • dList (smallList (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)))`. Rewrite using `[smallList_cons', sgnProd_cons', dList_append', cayMono_eq_dList', smul_mul_smul, mul_smul]`.
-/
theorem cayOp_pow_eq_sum (p q : ℕ) :
    cayOp p ℂ ^ q = ∑ τ : Fin q → Equiv.Perm (Fin p), sgnProd τ • dList (smallList τ) := by
  induction q with
  | zero => simp [smallList, sgnProd, dList]
  | succ q ih =>
    rw [pow_succ', ih, cayOp, Finset.sum_mul_sum,
      ← (Fin.consEquiv (fun _ => Equiv.Perm (Fin p))).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    change _ = sgnProd (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) •
      dList (smallList (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)))
    rw [smallList_cons', sgnProd_cons', dList_append', cayMono_eq_dList', smul_mul_smul, mul_smul]

end GlobalTheory.CayleyBlock
