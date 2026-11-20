import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding

namespace GlobalTheory.CompanionTheory.RgExhFin

open CompanionTheory.RgExh

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem simplePath_cons_iff {n : ℕ} (χ : Fin n → ℂ) (a : Fin n) (l : List (Fin n)) :
    SimplePath χ (a :: l) ↔ (∀ r, r ≠ a → χ r ≠ χ a) ∧ SimplePath (χ + Pi.single a 1) l :=
  Iff.rfl

/- English proof (translation)
Proceed by induction on `ss with`. Consider the case `nil`. Introduce `χ _ r s _ h`. Simplify using `at h`. Consider the case `cons a l ih`.

Introduce `χ hp r s hrs hmem`. Rewrite `hp` using `[simplePath_cons_iff]`. Take `⟨h1, h2⟩` from `hp`. Distinguish the cases in `hra : r = a`. Substitute `hra` using the available equality.

Conclude with `(h1 s (Ne.symm hrs)).symm`. Distinguish the cases in `hsa : s = a`. Substitute `hsa` using the available equality. Conclude with `h1 r hrs`. Establish `hmem' : r ∈ l ∨ s ∈ l`.

Simplify using `only [List.mem_cons] at hmem`. The claim follows by propositional logic. Establish `h3` using `ih _ h2 r s hrs hmem'`. Simplify `h3` using `[Pi.single_apply, hra, hsa]`.
-/
theorem simplePath_ne {n : ℕ} (ss : List (Fin n)) :
    ∀ χ : Fin n → ℂ, SimplePath χ ss → ∀ r s, r ≠ s → (r ∈ ss ∨ s ∈ ss) → χ r ≠ χ s := by
  induction ss with
  | nil =>
    intro χ _ r s _ h
    simp at h
  | cons a l ih =>
    intro χ hp r s hrs hmem
    rw [simplePath_cons_iff] at hp
    obtain ⟨h1, h2⟩ := hp
    by_cases hra : r = a
    · subst hra
      exact (h1 s (Ne.symm hrs)).symm
    by_cases hsa : s = a
    · subst hsa
      exact h1 r hrs
    have hmem' : r ∈ l ∨ s ∈ l := by
      simp only [List.mem_cons] at hmem
      tauto
    have h3 := ih _ h2 r s hrs hmem'
    simpa [Pi.single_apply, hra, hsa] using h3

/- English proof (translation)
Unfold `CompanionTheory.RgExh.Fin.SimpleDistinct`. Introduce `n χ ss hp hall r s hrs`. Assume the negation of the conclusion as `hne`. Conclude with `simplePath_ne ss χ hp r s hne (Or.inl (hall r)) hrs`.
-/
theorem simpleDistinct : CompanionTheory.RgExh.Fin.SimpleDistinct := by
  unfold CompanionTheory.RgExh.Fin.SimpleDistinct
  intro n χ ss hp hall r s hrs
  by_contra hne
  exact simplePath_ne ss χ hp r s hne (Or.inl (hall r)) hrs

end GlobalTheory.CompanionTheory.RgExhFin
