import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock

namespace UpperTheory.V.Cj.S

/- English proof (translation)
Introduce `E _ _ _ r s k l m₁ m₂ B₁ B₂ h₁ h₂`. Take `⟨ι, _, n, π, μ, hk, hn, hs, hi, hm, hB⟩` from `h₁`. Take `⟨κ, _, n', π', μ', hk', hn', hs', hi', hm', hB'⟩` from `h₂`. Use `⟨ι ⊕ κ, inferInstance, Sum.elim n n', fun i => Sum.rec (fun i => π i) (fun i => π' i) i, Sum.elim μ μ', ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.card_sum]`.

Conclude with `Nat.add_le_add hk hk'`. Introduce and unpack `(i | i)`. Conclude with `hn i`. Conclude with `hn' i`. Rewrite using `[Fintype.sum_sum_type, ← hs, ← hs']`.

Both sides reduce to the same expression. Introduce and unpack `(i | i) t`. Conclude with `hi i t`. Conclude with `hi' i t`. Introduce `t`.

Rewrite using `[Fintype.sum_sum_type]`. Use `show ∑ i, μ i t + ∑ i, μ' i t = m₁ t + m₂ t`. Rewrite using `[hm t, hm' t]`. Use `filter_upwards [hB, hB'] with w hw hw'`. Take `⟨C, hC, hCs⟩` from `hw`.

Take `⟨C', hC', hCs'⟩` from `hw'`. Use `⟨Sum.elim C C', ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(i | i)`. Conclude with `hC i`. Conclude with `hC' i`.

Rewrite using `[Fintype.sum_sum_type] show ∑ i, C i + ∑ i, C' i = B₁ w + B₂ w`. Rewrite using `[hCs, hCs']`.
-/
theorem suppAdd : SuppAdd := by
  intro E _ _ _ r s k l m₁ m₂ B₁ B₂ h₁ h₂
  obtain ⟨ι, _, n, π, μ, hk, hn, hs, hi, hm, hB⟩ := h₁
  obtain ⟨κ, _, n', π', μ', hk', hn', hs', hi', hm', hB'⟩ := h₂
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim n n', fun i => Sum.rec (fun i => π i) (fun i => π' i) i, Sum.elim μ μ',
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_sum]
    exact Nat.add_le_add hk hk'
  · rintro (i | i)
    · exact hn i
    · exact hn' i
  · rw [Fintype.sum_sum_type, ← hs, ← hs']
    rfl
  · rintro (i | i) t
    · exact hi i t
    · exact hi' i t
  · intro t
    rw [Fintype.sum_sum_type]
    show ∑ i, μ i t + ∑ i, μ' i t = m₁ t + m₂ t
    rw [hm t, hm' t]
  · filter_upwards [hB, hB'] with w hw hw'
    obtain ⟨C, hC, hCs⟩ := hw
    obtain ⟨C', hC', hCs'⟩ := hw'
    refine ⟨Sum.elim C C', ?_, ?_⟩
    · rintro (i | i)
      · exact hC i
      · exact hC' i
    · rw [Fintype.sum_sum_type]
      show ∑ i, C i + ∑ i, C' i = B₁ w + B₂ w
      rw [hCs, hCs']

end UpperTheory.V.Cj.S
