import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LinkExactAff
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ExactAtOfLinksOutsideExactAtOfConed
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.SubClosedAndPermAndLinearEquivInvariantUniM
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.ConsMemUniMIffMapSubSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.HomologicalStability.LinkExactnessStability.LinkInUniMEqShorterOfFormEqOne

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `R _ s n h j hj p hp`. Establish `hsub` using `(T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1`. Establish `hlow : ∀ x ∈ low R n, x j = 0`. Introduce `x hx`. Establish `h' : ∀ i, n ≤ i → x i = 0` using `hx`.

Conclude with `h' j hj`. Establish `haff : ∀ x ∈ aff R n j, x j = 1`. Introduce `x hx`. Establish `h' : ∀ i, n ≤ i → (x - Finsupp.single j (1 : R)) i = 0` using `hx`. Simplify `h' j hj` using `[sub_eq_zero]`.

Establish `hφ : ∀ x : ℕ →₀ R, (Finsupp.lapply j : (ℕ →₀ R) →ₗ[R] R) x = x j` using `fun x => rfl`. Use `exactAt_of_links_cone (ℕ →₀ R) (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) []) (low R n) (Finsupp.single j 1) ?_ ?_ p ?_` and prove the remaining obligations. Introduce `l hl l' hl'`. Take `⟨hl1, hl2⟩` from `hl`. Use `⟨fun x hx => hl1 x (hl'.subset hx), ?_⟩` and prove the remaining obligations.

Establish `hl2' : l ∈ uniM R (ℕ →₀ R)` using `hl2`. Conclude with `hsub l hl2' l' hl'`. Introduce `l hl`. Take `⟨hl1, hl2, hl3⟩` from `hl`. Establish `hl3' : l ∈ uniM R (ℕ →₀ R)` using `hl3`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `x hx`. Break down `List.mem_cons.mp hx with rfl | hx` into its components or cases. Use `right show (Finsupp.single j (1 : R) - Finsupp.single j 1) ∈ low R n`. Rewrite using `[sub_self]`.

Conclude with `fun i _ => Finsupp.zero_apply`. Conclude with `hl2 x hx`. Use `show Finsupp.single j (1 : R) :: l ∈ uniM R (ℕ →₀ R)`. Rewrite using `[T.cons_mem_uniM_iff_map_sub_smul R (ℕ →₀ R) (Finsupp.lapply j : (ℕ →₀ R) →ₗ[R] R) _ (by rw [hφ]; simp)]`. Use `hl3' using 2` and compare the differences between its conclusion and the goal.

Use `conv_rhs => rw [← List.map_id l]`. Apply `List.map_congr_left` to reduce the goal to its premises. Introduce `x hx`. Rewrite using `[hφ, hlow x (hl1 x hx), zero_smul, sub_zero]`. Both sides reduce to the same expression.

Introduce `τ hτ x hlast hx hlen`. Take `⟨hτS, hτU⟩` from `hτ`. Establish `hτU' : τ ∈ uniM R (ℕ →₀ R)` using `hτU`. Establish `hxτ : x ∈ τ` using `List.mem_of_getLast? hlast`. Establish `hxaff : x ∈ aff R n j` using `(hτS x hxτ).resolve_left hx`.

Establish `hx1 : (Finsupp.lapply j : (ℕ →₀ R) →ₗ[R] R) x = 1` using `by rw [hφ]; exact haff x hxaff`. Take `⟨τ', hτ'U, hlen', heq⟩` from `T.linkIn_uniM_eq_shorter_of_form_eq_one R (ℕ →₀ R) (Finsupp.lapply j : (ℕ →₀ R) →ₗ[R] R) (low R n) (fun y hy => by rw [hφ]; exact hlow y hy) τ hτU' x hxτ hx1`. Establish `hL : linkIn (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) []) (low R n) τ = linkIn (uniM R (ℕ →₀ R)) (low R n) τ`. Use extensionality with `w`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, _, h3⟩`. Conclude with `⟨h1, h3⟩`. Introduce and unpack `⟨h1, h3⟩`. Use `⟨h1, ?_, h3⟩` and prove the remaining obligations. Introduce `y hy`.

Establish `hy' : y ∈ τ ++ w` using `hy`. Break down `List.mem_append.mp hy' with hy | hy` into its components or cases. Conclude with `hτS y hy`. Conclude with `Or.inl (h1 y hy)`. Rewrite using `[hL, heq]`.

Conclude with `h τ' hτ'U (p - τ.length) (by omega)`.
-/
theorem exactAt_uniM_low_union_aff : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactLow R s n →
    ∀ j : ℕ, n ≤ j → ∀ p : ℕ, p + s ≤ n + 1 →
      ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) []) p := by
  intro R _ s n h j hj p hp
  have hsub := (T.subClosed_and_perm_and_linearEquiv_invariant_uniM R (ℕ →₀ R)).1
  have hlow : ∀ x ∈ low R n, x j = 0 := by
    intro x hx
    have h' : ∀ i, n ≤ i → x i = 0 := hx
    exact h' j hj
  have haff : ∀ x ∈ aff R n j, x j = 1 := by
    intro x hx
    have h' : ∀ i, n ≤ i → (x - Finsupp.single j (1 : R)) i = 0 := hx
    simpa [sub_eq_zero] using h' j hj
  have hφ : ∀ x : ℕ →₀ R, (Finsupp.lapply j : (ℕ →₀ R) →ₗ[R] R) x = x j := fun x => rfl
  refine exactAt_of_links_cone (ℕ →₀ R) (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) [])
    (low R n) (Finsupp.single j 1) ?_ ?_ p ?_
  · intro l hl l' hl'
    obtain ⟨hl1, hl2⟩ := hl
    refine ⟨fun x hx => hl1 x (hl'.subset hx), ?_⟩
    have hl2' : l ∈ uniM R (ℕ →₀ R) := hl2
    exact hsub l hl2' l' hl'
  · intro l hl
    obtain ⟨hl1, hl2, hl3⟩ := hl
    have hl3' : l ∈ uniM R (ℕ →₀ R) := hl3
    refine ⟨?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · right
        show (Finsupp.single j (1 : R) - Finsupp.single j 1) ∈ low R n
        rw [sub_self]
        exact fun i _ => Finsupp.zero_apply
      · exact hl2 x hx
    · show Finsupp.single j (1 : R) :: l ∈ uniM R (ℕ →₀ R)
      rw [T.cons_mem_uniM_iff_map_sub_smul R (ℕ →₀ R) (Finsupp.lapply j : (ℕ →₀ R) →ₗ[R] R) _ (by rw [hφ]; simp)]
      convert hl3' using 2
      conv_rhs => rw [← List.map_id l]
      apply List.map_congr_left
      intro x hx
      rw [hφ, hlow x (hl1 x hx), zero_smul, sub_zero]
      rfl
  · intro τ hτ x hlast hx hlen
    obtain ⟨hτS, hτU⟩ := hτ
    have hτU' : τ ∈ uniM R (ℕ →₀ R) := hτU
    have hxτ : x ∈ τ := List.mem_of_getLast? hlast
    have hxaff : x ∈ aff R n j := (hτS x hxτ).resolve_left hx
    have hx1 : (Finsupp.lapply j : (ℕ →₀ R) →ₗ[R] R) x = 1 := by rw [hφ]; exact haff x hxaff
    obtain ⟨τ', hτ'U, hlen', heq⟩ := T.linkIn_uniM_eq_shorter_of_form_eq_one R (ℕ →₀ R) (Finsupp.lapply j : (ℕ →₀ R) →ₗ[R] R) (low R n)
      (fun y hy => by rw [hφ]; exact hlow y hy) τ hτU' x hxτ hx1
    have hL : linkIn (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) []) (low R n) τ
        = linkIn (uniM R (ℕ →₀ R)) (low R n) τ := by
      ext w
      constructor
      · rintro ⟨h1, _, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        refine ⟨h1, ?_, h3⟩
        intro y hy
        have hy' : y ∈ τ ++ w := hy
        rcases List.mem_append.mp hy' with hy | hy
        · exact hτS y hy
        · exact Or.inl (h1 y hy)
    rw [hL, heq]
    exact h τ' hτ'U (p - τ.length) (by omega)

end GlobalTheory

section
open GlobalTheory.SeqCx Matrix
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.exactAt_uniM_low_union_aff`.
-/
theorem _root_.GlobalTheory.T.exactAt_link_nil_coordSubspace_union_translate : ∀ (R : Type) [CommRing R] (s n : ℕ), LinkExactLow R s n → ∀ j : ℕ, n ≤ j → ∀ p : ℕ, p + s ≤ n + 1 → ExactAt (linkIn (uniM R (ℕ →₀ R)) (low R n ∪ aff R n j) []) p := by
  first
  | exact @GlobalTheory.exactAt_uniM_low_union_aff
end
