import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `O _ _ _ _ _ _ _ _ ϖ hϖ`. Use `⟨fun x => ?_, fun a ha => ?_⟩` and prove the remaining obligations. Use `set s : ℕ → O := fun n => ∑ j ∈ Finset.range n, ϖ ^ j * x j with hs`. Set `C : ℕ → Set O` to `fun n => Set.range (fun b : O => s n + ϖ ^ n * b)`. Establish `hcpt : ∀ n, IsCompact (C n)` using `fun n => isCompact_range (continuous_const.add (continuous_const.mul continuous_id))`.

Establish `hdec : ∀ n, C (n + 1) ⊆ C n`. Introduce `n y ⟨b, hb⟩`. Use `⟨x n + ϖ * b, ?_⟩` and prove the remaining obligations. Rewrite using `[← hb]`. Simplify using `only [hs, Finset.sum_range_succ, pow_succ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hne : ∀ n, (C n).Nonempty` using `fun n => ⟨_, ⟨0, rfl⟩⟩`. Take `⟨a, ha⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hdec hne (hcpt 0) (fun n => (hcpt n).isClosed)`. Use `⟨a, fun n => ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `Set.mem_iInter.mp ha n`.

Conclude with `⟨b, by rw [← hb]; simp [hs]⟩`. Establish `hne : Ideal.span {ϖ} ≠ (⊤ : Ideal O)`. Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Conclude with `hϖ.not_isUnit`. Establish `h` using `Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {ϖ}) hne`.

Establish `: a ∈ ⨅ i, (Ideal.span {ϖ}) ^ i`. Rewrite using `[Submodule.mem_iInf]`. Introduce `i`. Take `⟨b, hb⟩` from `ha i`. Rewrite using `[Ideal.span_singleton_pow, hb]`.

Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)`. Rewrite `this` using `[h]`. Conclude with `(Submodule.mem_bot O).mp this`.
-/
theorem compact_dvr_complete_separated : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O] [CompactSpace O] [T2Space O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (ϖ : O), Irreducible ϖ → (∀ x : ℕ → O, ∃ a : O, ∀ n : ℕ, ∃ b : O, a - ∑ j ∈ Finset.range n, ϖ ^ j * x j = ϖ ^ n * b) ∧ (∀ a : O, (∀ n : ℕ, ∃ b : O, a = ϖ ^ n * b) → a = 0) := by
  intro O _ _ _ _ _ _ _ _ ϖ hϖ
  refine ⟨fun x => ?_, fun a ha => ?_⟩
  · set s : ℕ → O := fun n => ∑ j ∈ Finset.range n, ϖ ^ j * x j with hs
    let C : ℕ → Set O := fun n => Set.range (fun b : O => s n + ϖ ^ n * b)
    have hcpt : ∀ n, IsCompact (C n) := fun n =>
      isCompact_range (continuous_const.add (continuous_const.mul continuous_id))
    have hdec : ∀ n, C (n + 1) ⊆ C n := by
      intro n y ⟨b, hb⟩
      refine ⟨x n + ϖ * b, ?_⟩
      rw [← hb]
      simp only [hs, Finset.sum_range_succ, pow_succ]
      ring
    have hne : ∀ n, (C n).Nonempty := fun n => ⟨_, ⟨0, rfl⟩⟩
    obtain ⟨a, ha⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hdec hne
      (hcpt 0) (fun n => (hcpt n).isClosed)
    refine ⟨a, fun n => ?_⟩
    obtain ⟨b, hb⟩ := Set.mem_iInter.mp ha n
    exact ⟨b, by rw [← hb]; simp [hs]⟩
  · have hne : Ideal.span {ϖ} ≠ (⊤ : Ideal O) := by
      rw [Ne, Ideal.span_singleton_eq_top]; exact hϖ.not_isUnit
    have h := Ideal.iInf_pow_eq_bot_of_isLocalRing (Ideal.span {ϖ}) hne
    have : a ∈ ⨅ i, (Ideal.span {ϖ}) ^ i := by
      rw [Submodule.mem_iInf]
      intro i
      obtain ⟨b, hb⟩ := ha i
      rw [Ideal.span_singleton_pow, hb]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [h] at this
    exact (Submodule.mem_bot O).mp this

end GlobalTheory
