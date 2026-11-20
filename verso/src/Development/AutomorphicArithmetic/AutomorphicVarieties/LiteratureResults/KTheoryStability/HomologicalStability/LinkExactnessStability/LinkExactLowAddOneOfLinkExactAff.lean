import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqComplexExactAtOfAllLinksExactAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedAndPermAndLinearEquivInvariantUniM

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `x hx`. Break down `hx with hx | hx` into its components or cases. Introduce `i hi`. Conclude with `hx i (by omega)`. Introduce `i hi`.

Use `hx i (by omega)` as an intermediate fact. Simplify `this` using `[Finsupp.single_apply, show n ≠ i by omega]`.
-/
theorem low_union_aff_subset_low_succ (R : Type) [CommRing R] (n : ℕ) :
    low R n ∪ aff R n n ⊆ low R (n + 1) := by
  intro x hx
  rcases hx with hx | hx
  · intro i hi
    exact hx i (by omega)
  · intro i hi
    have := hx i (by omega)
    simpa [Finsupp.single_apply, show n ≠ i by omega] using this

/- English proof (translation)
Introduce `R _ s n h τ hτ p hp`. Establish `hsub : SubClosed (uniM R (ℕ →₀ R))` using `(T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1`. Apply `exactAt_of_links (ℕ →₀ R) _ (low R n ∪ aff R n n)` to reduce the goal to its premises. Introduce `l hl l' hl'`. Use `⟨fun x hx => hl.1 x (hl'.subset hx), hsub _ hl.2 _ ?_⟩` and prove the remaining obligations.

Simplify using `using hl'`. Introduce `τ1 hτ1 hlen`. Establish `heq : linkIn (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1)) τ) (low R n ∪ aff R n n) τ1 = linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n n) (τ ++ τ1)`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hw, -, h2⟩`. Use `⟨hw, ?_⟩` and prove the remaining obligations. Rewrite using `[List.append_assoc]`. Conclude with `h2`. Introduce and unpack `⟨hw, h2⟩`.

Use `⟨hw, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Break down `List.mem_append.mp hx with hx | hx` into its components or cases. Conclude with `hτ1.1 x hx`. Conclude with `low_union_aff_subset_low_succ R n (hw x hx)`. Rewrite using `[← List.append_assoc]`.

Conclude with `h2`. Rewrite using `[heq]`. Conclude with `h n le_rfl (τ ++ τ1) hτ1.2 (p - τ1.length) (by rw [List.length_append]; omega)`.
-/
theorem linkExactLow_succ_of_linkExactAff : ∀ (R : Type) [CommRing R] (s n : ℕ),
    LinkExactAff R s n → LinkExactLow R s (n + 1) := by
  intro R _ s n h τ hτ p hp
  have hsub : SubClosed (uniM R (ℕ →₀ R)) := (T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1
  apply exactAt_of_links (ℕ →₀ R) _ (low R n ∪ aff R n n)
  · intro l hl l' hl'
    refine ⟨fun x hx => hl.1 x (hl'.subset hx), hsub _ hl.2 _ ?_⟩
    simpa using hl'
  · intro τ1 hτ1 hlen
    have heq : linkIn (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1)) τ) (low R n ∪ aff R n n) τ1 =
        linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n n) (τ ++ τ1) := by
      ext w
      constructor
      · rintro ⟨hw, -, h2⟩
        refine ⟨hw, ?_⟩
        rw [List.append_assoc]
        exact h2
      · rintro ⟨hw, h2⟩
        refine ⟨hw, fun x hx => ?_, ?_⟩
        · rcases List.mem_append.mp hx with hx | hx
          · exact hτ1.1 x hx
          · exact low_union_aff_subset_low_succ R n (hw x hx)
        · rw [← List.append_assoc]
          exact h2
    rw [heq]
    exact h n le_rfl (τ ++ τ1) hτ1.2 (p - τ1.length) (by rw [List.length_append]; omega)

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.linkExactLow_succ_of_linkExactAff`. Consider the case `exact @GlobalTheory.low_union_aff_subset_low_succ`.
-/
theorem _root_.GlobalTheory.T.linkExactLow_add_one_of_linkExactAff : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactAff R s n → LinkExactLow R s (n + 1) := by
  first
  | exact @GlobalTheory.linkExactLow_succ_of_linkExactAff
  | exact @GlobalTheory.low_union_aff_subset_low_succ
end
