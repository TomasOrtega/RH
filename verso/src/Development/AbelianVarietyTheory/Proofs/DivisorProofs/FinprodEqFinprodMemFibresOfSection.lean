import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
theorem finprod_eq_finprod_mem_fibres_of_section :
    ∀ {α γ M : Type} [CommMonoid M] (p : α → γ) (S : Set α) (f : α → M),
      (∀ x, ∃! s, s ∈ S ∧ p s = p x) → (Function.mulSupport f).Finite →
        ∏ᶠ x, f x = ∏ᶠ s ∈ S, ∏ᶠ x ∈ {x | p x = p s}, f x := by
  intro α γ M _ p S f hS hf
  choose g hg using fun x => (hS x).exists
  have key : ∀ s ∈ S, ∀ x, p x = p s ↔ g x = s := by
    intro s hs x
    constructor
    · intro h
      exact (hS x).unique (hg x) ⟨hs, h.symm⟩
    · rintro rfl
      exact (hg x).2.symm
  set T := hf.toFinset with hT
  have hin : ∀ s ∈ S, ∏ᶠ x ∈ {x | p x = p s}, f x = ∏ x ∈ T with g x = s, f x := by
    intro s hs
    apply finprod_mem_eq_prod_of_subset
    · rintro x ⟨hx1, hx2⟩
      simp only [Finset.coe_filter, Set.mem_setOf_eq, hT, Set.Finite.mem_toFinset]
      exact ⟨hx2, (key s hs x).1 hx1⟩
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx
      exact (key s hs x).2 hx.2
  rw [finprod_mem_congr rfl hin, finprod_eq_prod_of_mulSupport_subset f (s := T) (by simp [hT])]
  rw [finprod_mem_eq_prod_of_subset (t := T.image g)]
  · exact (Finset.prod_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem g hi) f).symm
  · rintro s ⟨_, hs⟩
    rw [Function.mem_mulSupport] at hs
    obtain ⟨u, hu, _⟩ := Finset.exists_ne_one_of_prod_ne_one hs
    rw [Finset.mem_filter] at hu
    rw [Finset.coe_image]
    exact ⟨u, hu.1, hu.2⟩
  · intro s hs
    rw [Finset.coe_image] at hs
    obtain ⟨u, _, rfl⟩ := hs
    exact (hg u).1

end GlobalTheory
