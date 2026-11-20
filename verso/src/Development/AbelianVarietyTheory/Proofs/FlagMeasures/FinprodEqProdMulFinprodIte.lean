import Mathlib

namespace GlobalTheory.FinprodProdMulIte

open Classical in

/- English proof (translation)
Establish `hsub₁ : Function.mulSupport (fun p => if p ∈ S₁ then f p else (1 : ℂ)) ⊆ (S₁ : Set ι)`. Introduce `p hp`. Assume the negation of the conclusion as `h`. Establish `h' : p ∉ S₁` using `h`. Conclude with `hp (by simp [h'])`.

Establish `hsub₂ : Function.mulSupport (fun p => if p ∈ S₁ then (1 : ℂ) else g p) ⊆ Function.mulSupport f`. Introduce `p hp`. Distinguish the cases in `h : p ∈ S₁`. Conclude with `absurd (by simp [h]) hp`. Introduce `h1`.

Conclude with `hp (by simp [h, ← hfg p h, h1])`. Establish `h₁ : ∏ᶠ p, (if p ∈ S₁ then f p else (1 : ℂ)) = ∏ p ∈ S₁, f p`. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ hsub₁]`. Conclude with `Finset.prod_congr rfl fun p hp => by simp [hp]`. Rewrite using `[← h₁, ← finprod_mul_distrib (S₁.finite_toSet.subset hsub₁) (hf.subset hsub₂)]`.

Use `finprod_congr fun p => ?_` and prove the remaining obligations. Distinguish the cases in `h : p ∈ S₁`. Simplify using `[h]`. Simplify using `[h, hfg p h]`.
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
