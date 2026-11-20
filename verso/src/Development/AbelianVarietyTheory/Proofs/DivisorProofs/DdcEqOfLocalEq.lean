import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPosFrameQuotIn

set_option autoImplicit false

open Set Matrix Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.CxForm GlobalTheory.SecForm
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.SecForm.DdcGerm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem repr_eventuallyEq {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) (S : Finset (Fin (n + n))) :
    (fun x => (bas n).repr (α x) S) =ᶠ[𝓝 v] fun x => (bas n).repr (β x) S :=
  h.mono fun x hx => by simp only [hx]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem delAt_germ {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : delAt α v = delAt β v := by
  simp only [delAt, coefwise]
  refine Finset.sum_congr rfl fun a _ => congrArg _ (Finset.sum_congr rfl fun S _ => ?_)
  rw [del_congr (repr_eventuallyEq h S)]

/- English proof (translation)
Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem dbarAt_germ {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : dbarAt α v = dbarAt β v := by
  simp only [dbarAt, coefwise]
  refine Finset.sum_congr rfl fun a _ => congrArg _ (Finset.sum_congr rfl fun S _ => ?_)
  rw [dbar_congr (repr_eventuallyEq h S)]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem loc_dbar_of_mem {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (α : A.Fld) (i : A.ι) {v : V n}
    (hv : v ∈ (A.e i).target) : A.loc (A.dbar α) i v = dbarAt (A.loc α i) v := by
  rw [HolAtlas.loc, dif_pos hv]
  exact congrArg (dbarAt (A.loc α i)) ((A.e i).right_inv hv)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities.
-/
theorem ddc_eq_of_eventuallyEq : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (α : A.Fld) (x : A.Pt)
    (f : V n → Alt n), A.loc α x.1.1 =ᶠ[𝓝 x.crd] f → A.ddc α x = kappa • delAt (dbarAt f) x.crd := by
  intro M _ n A α x f h
  have ht : (A.e x.1.1).target ∈ 𝓝 x.crd := (A.e x.1.1).open_target.mem_nhds ((A.e x.1.1).map_source x.2)
  have key : A.loc (A.dbar α) x.1.1 =ᶠ[𝓝 x.crd] dbarAt f := by
    filter_upwards [ht, h.eventuallyEq_nhds] with v hv hv'
    rw [loc_dbar_of_mem A α _ hv, dbarAt_germ hv']
  change kappa • delAt (A.loc (A.dbar α) x.1.1) x.crd = _
  rw [delAt_germ key]

end GlobalTheory.SecForm.DdcGerm
