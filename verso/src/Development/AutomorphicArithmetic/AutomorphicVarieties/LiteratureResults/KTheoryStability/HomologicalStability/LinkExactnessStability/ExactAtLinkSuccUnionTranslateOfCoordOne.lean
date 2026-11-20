import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SeqComplexExactAtOfAllLinksExactAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedAndPermAndLinearEquivInvariantUniM
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.LinkInUniMEqShorterOfFormEqOne

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

/- English proof (translation)
Introduce and unpack `x (hx | hx)`. Conclude with `Or.inl fun i hi => hx i (by omega)`. Conclude with `Or.inr fun i hi => hx i (by omega)`.
-/
theorem low_aff_subset_succ (R : Type) [CommRing R] (n j : ℕ) :
    low R n ∪ aff R n j ⊆ low R (n + 1) ∪ aff R (n + 1) j := by
  rintro x (hx | hx)
  · exact Or.inl fun i hi => hx i (by omega)
  · exact Or.inr fun i hi => hx i (by omega)

/- English proof (translation)
Introduce `x hx`. Rewrite using `[Finsupp.lapply_apply]`. Break down `hx with hx | hx` into its components or cases. Conclude with `hx n le_rfl`. Use `hx n le_rfl` as an intermediate fact.

Simplify `this` using `[Finsupp.single_apply, show j ≠ n by omega]`.
-/
theorem coord_vanish_low_aff (R : Type) [CommRing R] (n j : ℕ) (hj : n + 1 ≤ j) :
    ∀ x ∈ low R n ∪ aff R n j, (Finsupp.lapply n : (ℕ →₀ R) →ₗ[R] R) x = 0 := by
  intro x hx
  rw [Finsupp.lapply_apply]
  rcases hx with hx | hx
  · exact hx n le_rfl
  · have := hx n le_rfl
    simpa [Finsupp.single_apply, show j ≠ n by omega] using this

/- English proof (translation)
Introduce `R _ s n h j hj τ hτ v hv hvn p hp`. Establish `hsub : SubClosed (uniM R (ℕ →₀ R))` using `(T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1`. Establish `hlenpos` using `List.length_pos_of_mem hv`. Apply `exactAt_of_links (ℕ →₀ R) _ (low R n ∪ aff R n j)` to reduce the goal to its premises. Introduce `l hl l' hl'`.

Use `⟨fun x hx => hl.1 x (hl'.subset hx), hsub _ hl.2 _ ?_⟩` and prove the remaining obligations. Simplify using `using hl'`. Introduce `τ1 hτ1 hlen`. Establish `heq : linkIn (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) (low R n ∪ aff R n j) τ1 = linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) (τ ++ τ1)`. Use extensionality with `w`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hw, -, h2⟩`. Use `⟨hw, ?_⟩` and prove the remaining obligations. Rewrite using `[List.append_assoc]`. Conclude with `h2`.

Introduce and unpack `⟨hw, h2⟩`. Use `⟨hw, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Break down `List.mem_append.mp hx with hx | hx` into its components or cases. Conclude with `hτ1.1 x hx`. Conclude with `low_aff_subset_succ R n j (hw x hx)`.

Rewrite using `[← List.append_assoc]`. Conclude with `h2`. Rewrite using `[heq]`. Take `⟨τ', hτ', hl', heq'⟩` from `T.linkIn_uniM_eq_shorter_of_form_eq_one R (ℕ →₀ R) (Finsupp.lapply n) (low R n ∪ aff R n j) (coord_vanish_low_aff R n j hj) (τ ++ τ1) hτ1.2 v (List.mem_append_left _ hv) (by rw [Finsupp.lapply_apply]; exact hvn)`. Rewrite using `[heq']`.

Rewrite `hl'` using `[List.length_append]`. Conclude with `h j (by omega) τ' hτ' (p - τ1.length) (by omega)`.
-/
theorem linkIn_exactAt_of_coord_one : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactAff R s n →
    ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), ∀ v ∈ τ, v n = 1 → ∀ p : ℕ,
    p + s + τ.length ≤ n + 2 →
    ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  intro R _ s n h j hj τ hτ v hv hvn p hp
  have hsub : SubClosed (uniM R (ℕ →₀ R)) := (T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1
  have hlenpos := List.length_pos_of_mem hv
  apply exactAt_of_links (ℕ →₀ R) _ (low R n ∪ aff R n j)
  · intro l hl l' hl'
    refine ⟨fun x hx => hl.1 x (hl'.subset hx), hsub _ hl.2 _ ?_⟩
    simpa using hl'
  · intro τ1 hτ1 hlen
    have heq : linkIn (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ)
        (low R n ∪ aff R n j) τ1 = linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) (τ ++ τ1) := by
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
          · exact low_aff_subset_succ R n j (hw x hx)
        · rw [← List.append_assoc]
          exact h2
    rw [heq]
    obtain ⟨τ', hτ', hl', heq'⟩ := T.linkIn_uniM_eq_shorter_of_form_eq_one R (ℕ →₀ R) (Finsupp.lapply n) (low R n ∪ aff R n j)
      (coord_vanish_low_aff R n j hj) (τ ++ τ1) hτ1.2 v (List.mem_append_left _ hv)
      (by rw [Finsupp.lapply_apply]; exact hvn)
    rw [heq']
    rw [List.length_append] at hl'
    exact h j (by omega) τ' hτ' (p - τ1.length) (by omega)

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.SeqCx.linkIn_exactAt_of_coord_one`. Consider the case `exact @GlobalTheory.SeqCx.coord_vanish_low_aff`. Consider the case `exact @GlobalTheory.SeqCx.low_aff_subset_succ`.
-/
theorem _root_.GlobalTheory.T.exactAt_link_succ_union_translate_of_coord_one : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactAff R s n → ∀ j : ℕ, n + 1 ≤ j → ∀ τ ∈ uniM R (ℕ →₀ R), ∀ v ∈ τ, v n = 1 → ∀ p : ℕ, p + s + τ.length ≤ n + 2 → ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R (n + 1) ∪ aff R (n + 1) j) τ) p := by
  first
  | exact @GlobalTheory.SeqCx.linkIn_exactAt_of_coord_one
  | exact @GlobalTheory.SeqCx.coord_vanish_low_aff
  | exact @GlobalTheory.SeqCx.low_aff_subset_succ
end
