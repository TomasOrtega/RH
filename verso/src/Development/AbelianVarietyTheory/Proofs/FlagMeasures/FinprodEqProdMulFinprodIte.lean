import Mathlib

namespace GlobalTheory.FinprodProdMulIte

open Classical in

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem finprod_eq_prod_mul_finprod_ite {ι : Type} (S₁ : Finset ι) (f g : ι → ℂ)
    (hf : (Function.mulSupport f).Finite) (hfg : ∀ p, p ∉ S₁ → f p = g p) :
    ∏ᶠ p, f p = (∏ p ∈ S₁, f p) * ∏ᶠ p, (if p ∈ S₁ then (1 : ℂ) else g p) := by
  have hsub₁ : Function.mulSupport (fun p => if p ∈ S₁ then f p else (1 : ℂ)) ⊆ (S₁ : Set ι) := by
    intro p hp
    by_contra h
    have h' : p ∉ S₁ := h
    exact hp (by simp [h'])
  have hsub₂ : Function.mulSupport (fun p => if p ∈ S₁ then (1 : ℂ) else g p)
      ⊆ Function.mulSupport f := by
    intro p hp
    by_cases h : p ∈ S₁
    · exact absurd (by simp [h]) hp
    · intro h1
      exact hp (by simp [h, ← hfg p h, h1])
  have h₁ : ∏ᶠ p, (if p ∈ S₁ then f p else (1 : ℂ)) = ∏ p ∈ S₁, f p := by
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub₁]
    exact Finset.prod_congr rfl fun p hp => by simp [hp]
  rw [← h₁, ← finprod_mul_distrib (S₁.finite_toSet.subset hsub₁) (hf.subset hsub₂)]
  refine finprod_congr fun p => ?_
  by_cases h : p ∈ S₁
  · simp [h]
  · simp [h, hfg p h]

end GlobalTheory.FinprodProdMulIte
