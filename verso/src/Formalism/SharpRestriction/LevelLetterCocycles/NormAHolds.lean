import Formalism.SharpRestriction.LevelLetterCocycles.MixedPositionHypothesis

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

/- English proof (translation)
Introduce `T₁ T₂ F r S η m h up b hA hJ`. Unfold `Formalism.MainNotions.ElementDenominator.HypA at hA`. Take `⟨hc1, hc2, hon, _, hj1, hηb, hsum, hjh, hposition⟩` from `hA`. Establish `hT1 : ∀ τ, JumpsInV (P.PD K) T₁.ρ τ (deep (up τ) (min (b τ) (h + 1)) S ∪ Set.Icc (-((min η h : ℕ) : ℤ)) (min η h : ℕ))`. Introduce `τ a ha`.

Establish `ha1` using `hj1 τ a ha`. Establish `hah` using `hjh τ a ha`. Simplify using `only [Set.mem_Icc] at hah`. Break down `ha1 with h1 | h1` into its components or cases. Use `left`.

Unfold `deep at h1 ⊢`. Apply the tactic sequence `split_ifs at h1 ⊢ <;> simp only [Set.mem_Icc] at h1 ⊢ <;> push_cast <;> omega`. Use `right`. Simplify using `only [Set.mem_Icc] at h1 ⊢`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers. Establish `hj2h : ∀ τ, JumpsInV (P.PD K) T₂.ρ τ (Set.Icc (-(h : ℤ)) h)` using `fun τ => hJ τ _ (hjh τ)`. Use `⟨min η h, h + S + 1, fun τ => min (b τ) (h + 1), min_le_left _ _, le_rfl, ?_⟩` and prove the remaining obligations. Use `⟨hc1, hc2, hon, hT1, fun τ => hJ τ _ (hT1 τ), fun τ => ?_, fun τ => ?_, by omega, fun τ => ?_, hposition⟩` and prove the remaining obligations. Use `hηb τ show min η h < min (b τ) (h + 1)` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `show min (b τ) (h + 1) + S ≤ h + S + 1`. Use linear arithmetic over natural numbers and integers. Use `le_of_eq_of_le ?_ (hsum τ)` and prove the remaining obligations. Apply `Finset.sum_subset` to reduce the goal to its premises.

Introduce `x hx`. Simplify using `only [Finset.mem_Icc] at hx ⊢`. Move the coercions through the operations in `at hx`. Use linear arithmetic over natural numbers and integers. Introduce `x hx hx'`.

Simplify using `only [Finset.mem_Icc] at hx hx'`. Move the coercions through the operations in `at hx'`. Establish `hnj : ¬ IsJumpV (P.PD K) T₂.ρ τ x`. Introduce `hj`. Establish `h2` using `hj2h τ x hj`.

Simplify using `only [Set.mem_Icc] at h2`. Use linear arithmetic over natural numbers and integers. Unfold `IsJumpV at hnj`. Use `push_neg at hnj`. Unfold `multV`.

Rewrite using `[hnj, sub_self]`.
-/
theorem normA_holds {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) : normA P K LL := by
  intro T₁ T₂ F r S η m h up b hA hJ
  unfold Formalism.MainNotions.ElementDenominator.HypA at hA
  obtain ⟨hc1, hc2, hon, _, hj1, hηb, hsum, hjh, hposition⟩ := hA
  have hT1 : ∀ τ, JumpsInV (P.PD K) T₁.ρ τ
      (deep (up τ) (min (b τ) (h + 1)) S ∪ Set.Icc (-((min η h : ℕ) : ℤ)) (min η h : ℕ)) := by
    intro τ a ha
    have ha1 := hj1 τ a ha
    have hah := hjh τ a ha
    simp only [Set.mem_Icc] at hah
    rcases ha1 with h1 | h1
    · left
      unfold deep at h1 ⊢
      split_ifs at h1 ⊢ <;> simp only [Set.mem_Icc] at h1 ⊢ <;> push_cast <;> omega
    · right
      simp only [Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hj2h : ∀ τ, JumpsInV (P.PD K) T₂.ρ τ (Set.Icc (-(h : ℤ)) h) := fun τ => hJ τ _ (hjh τ)
  refine ⟨min η h, h + S + 1, fun τ => min (b τ) (h + 1), min_le_left _ _, le_rfl, ?_⟩
  refine ⟨hc1, hc2, hon, hT1, fun τ => hJ τ _ (hT1 τ), fun τ => ?_, fun τ => ?_, by omega,
    fun τ => ?_, hposition⟩
  · have := hηb τ
    show min η h < min (b τ) (h + 1)
    omega
  · show min (b τ) (h + 1) + S ≤ h + S + 1
    omega
  · refine le_of_eq_of_le ?_ (hsum τ)
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      push_cast at hx
      omega
    · intro x hx hx'
      simp only [Finset.mem_Icc] at hx hx'
      push_cast at hx'
      have hnj : ¬ IsJumpV (P.PD K) T₂.ρ τ x := by
        intro hj
        have h2 := hj2h τ x hj
        simp only [Set.mem_Icc] at h2
        omega
      unfold IsJumpV at hnj
      push_neg at hnj
      unfold multV
      rw [hnj, sub_self]

/- English proof (translation)
Introduce `l _ _ K LL _`. Conclude with `normA_holds (D.loc l) K LL`.
-/
theorem normR_holds (D : D7) : normR D := by
  intro l _ _ K LL _
  exact normA_holds (D.loc l) K LL

end Formalism.MainNotions.N.Ln34

end
