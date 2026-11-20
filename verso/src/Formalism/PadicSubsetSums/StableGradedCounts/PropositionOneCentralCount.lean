import Formalism.PadicSubsetSums.StableGradedCounts.IRRExcludedCount

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
Introduce `N Y P hN hY hP hcard`. Establish `hb0 : (0 : ℝ) ≤ (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1))`. Use `Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)` as an intermediate fact. Check the signs of the components of the expression. Establish `hne : P.Nonempty`.

Rewrite using `[← Finset.card_pos]`. Establish `: (0 : ℝ) < P.card` using `lt_of_le_of_lt hb0 hcard`. Conclude with `this` after adjusting the coercions. Take `⟨g₁, hg₁⟩` from `hne`. Use `set S := P.filter (fun g => ¬ Disjoint (BB g₁ N) (BB g N)) with hSdef`.

Establish `hS` using `excluded_count_bound N g₁ Y S hN hY (hP g₁ hg₁).1 (by`. Introduce `g hg`. Take `⟨h1, h2⟩` from `Finset.mem_filter.mp hg`. Conclude with `⟨(hP g h1).1, (hP g h1).2.1, (hP g h1).2.2, h2⟩)`. Establish `hlt : S.card < P.card` using `by exact_mod_cast lt_of_le_of_lt hS hcard`.

Choose the witnesses or unpack the hypotheses as in `⟨g₂, hg₂, hn⟩ : ∃ g₂ ∈ P, g₂ ∉ S := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Conclude with `absurd (Finset.card_le_card (fun g hg => hcon g hg)) (not_le.mpr hlt)`. Establish `hd : Disjoint (BB g₁ N) (BB g₂ N)`.

Assume the negation of the conclusion as `h`. Conclude with `hn (Finset.mem_filter.mpr ⟨hg₂, h⟩)`. Use `⟨g₁, hg₁, g₂, hg₂, ?_, hd⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Establish `hmem : g₁ ∈ BB g₁ N` using `by simp [BB]`.

Conclude with `Finset.disjoint_left.mp hd hmem hmem`.
-/
theorem proposition_one_central_count : Prop1Core := by
  classical
  intro N Y P hN hY hP hcard
  have hb0 : (0 : ℝ) ≤ (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)
    positivity
  have hne : P.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < P.card := lt_of_le_of_lt hb0 hcard
    exact_mod_cast this
  obtain ⟨g₁, hg₁⟩ := hne
  set S := P.filter (fun g => ¬ Disjoint (BB g₁ N) (BB g N)) with hSdef
  have hS := excluded_count_bound N g₁ Y S hN hY (hP g₁ hg₁).1 (by
    intro g hg
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hg
    exact ⟨(hP g h1).1, (hP g h1).2.1, (hP g h1).2.2, h2⟩)
  have hlt : S.card < P.card := by exact_mod_cast lt_of_le_of_lt hS hcard
  obtain ⟨g₂, hg₂, hn⟩ : ∃ g₂ ∈ P, g₂ ∉ S := by
    by_contra hcon
    push Not at hcon
    exact absurd (Finset.card_le_card (fun g hg => hcon g hg)) (not_le.mpr hlt)
  have hd : Disjoint (BB g₁ N) (BB g₂ N) := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨hg₂, h⟩)
  refine ⟨g₁, hg₁, g₂, hg₂, ?_, hd⟩
  rintro rfl
  have hmem : g₁ ∈ BB g₁ N := by simp [BB]
  exact Finset.disjoint_left.mp hd hmem hmem

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
