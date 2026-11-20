import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.TorsionRankCounts.RankCount

open NumberField UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Up CategoryTheory

/- English proof (translation)
Introduce `Y T B _ _ _ _ β g c hc S hS`. Use `choose! y hy using hS`. Use `Fintype.ofFinite T` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.card_le_mul_card_image` to reduce the goal to its premises.

Introduce `t _`. Break down `(S.filter (fun s => β (y s) = t)).eq_empty_or_nonempty with hF | ⟨s₀, hs₀⟩` into its components or cases. Rewrite using `[hF]`. Simplify using the standard rewrite rules. Rewrite using `[← Finset.card_image_of_injective _ (sub_left_injective (b := s₀))]`.

Apply `hc` to reduce the goal to its premises. Introduce `u hu`. Take `⟨s, hs, rfl⟩` from `Finset.mem_image.1 hu`. Establish `hs'` using `Finset.mem_filter.1 hs`. Establish `hs₀'` using `Finset.mem_filter.1 hs₀`.

Use `⟨y s - y s₀, by rw [map_sub, hs'.2, hs₀'.2, sub_self], ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, ← hy s hs'.1, ← hy s₀ hs₀'.1]`. Use `_ ≤ c * Nat.card T := by`. Apply `Nat.mul_le_mul_left` to reduce the goal to its premises. Rewrite using `[Nat.card_eq_fintype_card]`.

Conclude with `Finset.card_le_univ _`.
-/
theorem UpperTheory.V.ZK.Up.fibCount : UpperTheory.V.ZK.Up.FibCount := by
  intro Y T B _ _ _ _ β g c hc S hS
  classical
  choose! y hy using hS
  have := Fintype.ofFinite T
  calc S.card ≤ c * (S.image (fun s => β (y s))).card := by
        apply Finset.card_le_mul_card_image
        intro t _
        rcases (S.filter (fun s => β (y s) = t)).eq_empty_or_nonempty with hF | ⟨s₀, hs₀⟩
        · rw [hF]
          simp
        · rw [← Finset.card_image_of_injective _ (sub_left_injective (b := s₀))]
          apply hc
          intro u hu
          obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hu
          have hs' := Finset.mem_filter.1 hs
          have hs₀' := Finset.mem_filter.1 hs₀
          refine ⟨y s - y s₀, by rw [map_sub, hs'.2, hs₀'.2, sub_self], ?_⟩
          rw [map_sub, ← hy s hs'.1, ← hy s₀ hs₀'.1]
    _ ≤ c * Nat.card T := by
        apply Nat.mul_le_mul_left
        rw [Nat.card_eq_fintype_card]
        exact Finset.card_le_univ _
