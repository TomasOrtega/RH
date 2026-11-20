import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

set_option autoImplicit false

open GlobalTheory.CxForm

namespace GlobalTheory.ExactZero

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem eq_algebraMap_of_isType {n : ℕ} {a : Alt n} (h : IsType 0 0 a) : ∃ c : ℂ, a = algebraMap ℂ (Alt n) c := by
  refine ⟨(bas n).repr a ∅, (bas n).ext_elem fun S => ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, ← bas_empty, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply]
  split_ifs with hS
  · rw [← hS, smul_eq_mul, mul_one]
  · rw [smul_zero]
    by_contra h0
    obtain ⟨h₁, h₂⟩ := h S h0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h₁ h₂
    refine hS (Finset.eq_empty_of_forall_notMem fun i hi => ?_).symm
    exact h₂ hi (not_lt.1 (h₁ hi))

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem algebraMapInv_delAt {n : ℕ} (u : ReciprocityTheory.L2DbarEstimates.V n → Alt n) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    ExteriorAlgebra.algebraMapInv (delAt u v) = 0 := by
  simp [delAt, dz, map_sum, ExteriorAlgebra.algebraMapInv]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem algebraMapInv_dbarAt {n : ℕ} (u : ReciprocityTheory.L2DbarEstimates.V n → Alt n) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    ExteriorAlgebra.algebraMapInv (dbarAt u v) = 0 := by
  simp [dbarAt, dzb, map_sum, ExteriorAlgebra.algebraMapInv]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_of_isExact_sub : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (α β : A.Fld),
    (∀ x, IsType 0 0 (α x)) → (∀ x, IsType 0 0 (β x)) → A.IsExact (α - β) → α = β := by
  intro M _ n A α β hα hβ ⟨u, w, _, _, e⟩
  funext x
  obtain ⟨c, hc⟩ := eq_algebraMap_of_isType (hα x)
  obtain ⟨d, hd⟩ := eq_algebraMap_of_isType (hβ x)
  have h := congrArg (fun γ : A.Fld => ExteriorAlgebra.algebraMapInv (γ x)) e
  simp only [Pi.sub_apply, Pi.add_apply, HolAtlas.del, HolAtlas.dbar, map_add, map_sub, algebraMapInv_delAt,
    algebraMapInv_dbarAt, hc, hd, AlgHom.commutes, add_zero, sub_eq_zero] at h
  rw [hc, hd]
  exact congrArg _ h

end GlobalTheory.ExactZero
