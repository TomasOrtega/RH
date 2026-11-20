import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.LinkExactLowAddOneOfLinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkNilCoordSubspaceUnionTranslate
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtLinkInSuccUnionTranslateOfNeNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExistsMemTranslateUnimodularPairOfStableRangeLe

open GlobalTheory.SeqCx Matrix UpperTheory.V.KL

/- English proof (translation)
Introduce `c hc _`. Establish `hc'` using `(Finsupp.mem_supported _ _).mp hc`. Use `⟨Finsupp.single [x] (c []), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[chains, Finsupp.mem_supported]`. Introduce `l hl`.

Establish `hl'` using `Finsupp.support_single_subset hl`. Simplify using `only [Finset.mem_singleton] at hl'`. Substitute `hl'` using the available equality. Conclude with `⟨hx, rfl⟩`. Establish `hcs : c = Finsupp.single [] (c [])`.

Use extensionality with `l`. Distinguish the cases in `hl : l = []`. Substitute `hl` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Finsupp.single_apply, if_neg (Ne.symm hl)]`.

Assume the negation of the conclusion as `hne`. Establish `hmem` using `hc' (Finsupp.mem_support_iff.mpr hne)`. Conclude with `hl (List.length_eq_zero_iff.mp hmem.2)`. Rewrite using `[bd, Finsupp.linearCombination_single]`. Use `conv_rhs => rw [hcs]`.

Simplify using the standard rewrite rules.
-/
private theorem exactAt_zero_of_singleton_mem' {V : Type} (F : Set (List V)) (x : V) (hx : [x] ∈ F) :
    ExactAt F 0 := by
  intro c hc _
  have hc' := (Finsupp.mem_supported _ _).mp hc
  refine ⟨Finsupp.single [x] (c []), ?_, ?_⟩
  · rw [chains, Finsupp.mem_supported]
    intro l hl
    have hl' := Finsupp.support_single_subset hl
    simp only [Finset.mem_singleton] at hl'
    subst hl'
    exact ⟨hx, rfl⟩
  · have hcs : c = Finsupp.single [] (c []) := by
      ext l
      by_cases hl : l = []
      · subst hl
        simp
      · rw [Finsupp.single_apply, if_neg (Ne.symm hl)]
        by_contra hne
        have hmem := hc' (Finsupp.mem_support_iff.mpr hne)
        exact hl (List.length_eq_zero_iff.mp hmem.2)
    rw [bd, Finsupp.linearCombination_single]
    conv_rhs => rw [hcs]
    simp

/- English proof (translation)
Introduce `R _ s h hs n`. Proceed by induction on `n with`. Consider the case `zero`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `τ _ p hp`.

Use linear arithmetic over natural numbers and integers. Introduce `j hj τ hτ p hp`. Consider the cases of `τ with`. Consider the case `nil`. Conclude with `GlobalTheory.T.exactAt_link_nil_coordSubspace_union_translate R s 0 (fun τ _ p hp => by omega) j hj p (by simpa using hp)`.

Consider the case `cons v τ`. Simplify using `at hp`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`. Take `⟨_, hA⟩` from `ih`.

Establish `hL' : LinkExactLow R s (n + 1)` using `GlobalTheory.T.linkExactLow_add_one_of_linkExactAff R s n hA`. Use `⟨hL', ?_⟩` and prove the remaining obligations. Introduce `j hj τ hτ p hp`. Consider the cases of `τ with`. Consider the case `nil`.

Conclude with `GlobalTheory.T.exactAt_link_nil_coordSubspace_union_translate R s (n + 1) hL' j hj p (by simpa using hp)`. Consider the case `cons v τ`. Distinguish the cases in `hsn : s ≤ n`. Conclude with `GlobalTheory.T.exactAt_linkIn_succ_union_translate_of_ne_nil R s h n hsn hA j hj (v :: τ) hτ (List.cons_ne_nil _ _) p hp`. Simplify using `only [List.length_cons] at hp`.

Establish `hp0 : p = 0` using `by omega`. Establish `hτ0 : τ = []` using `List.length_eq_zero_iff.mp (by omega)`. Substitute `hp0` using the available equality. Substitute `hτ0` using the available equality. Take `⟨x, hx, hvx⟩` from `GlobalTheory.T.exists_mem_translate_unimodular_pair_of_stableRangeLe R s h (n + 1) j (by omega) hj v hτ`.

Conclude with `exactAt_zero_of_singleton_mem' _ x ⟨fun y hy => by`. Simplify using `only [List.mem_singleton] at hy`. Substitute `hy` using the available equality. Conclude with `Or.inr hx, by simpa using hvx⟩`.
-/
theorem GlobalTheory.SeqCx.linkExact_of_stableRangeLe : ∀ (R : Type) [CommRing R] (s : ℕ), StableRangeLe R s → 1 ≤ s →
    ∀ n : ℕ, LinkExactLow R s n ∧ LinkExactAff R s n := by
  intro R _ s h hs n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro τ _ p hp
      omega
    · intro j hj τ hτ p hp
      cases τ with
      | nil =>
        exact GlobalTheory.T.exactAt_link_nil_coordSubspace_union_translate R s 0 (fun τ _ p hp => by omega) j hj p (by simpa using hp)
      | cons v τ =>
        simp at hp
        omega
  | succ n ih =>
    obtain ⟨_, hA⟩ := ih
    have hL' : LinkExactLow R s (n + 1) := GlobalTheory.T.linkExactLow_add_one_of_linkExactAff R s n hA
    refine ⟨hL', ?_⟩
    intro j hj τ hτ p hp
    cases τ with
    | nil =>
      exact GlobalTheory.T.exactAt_link_nil_coordSubspace_union_translate R s (n + 1) hL' j hj p (by simpa using hp)
    | cons v τ =>
      by_cases hsn : s ≤ n
      · exact GlobalTheory.T.exactAt_linkIn_succ_union_translate_of_ne_nil R s h n hsn hA j hj (v :: τ) hτ (List.cons_ne_nil _ _) p hp
      · simp only [List.length_cons] at hp
        have hp0 : p = 0 := by omega
        have hτ0 : τ = [] := List.length_eq_zero_iff.mp (by omega)
        subst hp0
        subst hτ0
        obtain ⟨x, hx, hvx⟩ := GlobalTheory.T.exists_mem_translate_unimodular_pair_of_stableRangeLe R s h (n + 1) j (by omega) hj v hτ
        exact exactAt_zero_of_singleton_mem' _ x ⟨fun y hy => by
          simp only [List.mem_singleton] at hy
          subst hy
          exact Or.inr hx, by simpa using hvx⟩

section
open GlobalTheory.SeqCx Matrix UpperTheory.V.KL
end
