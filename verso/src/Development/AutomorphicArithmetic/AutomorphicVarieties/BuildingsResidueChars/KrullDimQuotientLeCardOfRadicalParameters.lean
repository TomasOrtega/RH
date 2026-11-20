import Mathlib

open IsLocalRing

/- English proof (translation)
Introduce `B _ _ _ q κ _ x hx h`. Distinguish the cases in `hq : q = ⊤`. Substitute `hq` using the available equality. Rewrite using `[ringKrullDim_eq_bot_of_subsingleton]`. Conclude with `bot_le`.

Use `haveI : Nontrivial (B ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hq`. Use `haveI : IsLocalRing (B ⧸ q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective`. Use `haveI : IsLocalHom (Ideal.Quotient.mk q) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective`. Set `s : Set (B ⧸ q)` to `Set.range (fun k => Ideal.Quotient.mk q (x k))`. Establish `hs : s.Finite` using `Set.finite_range _`.

Establish `hmin : maximalIdeal (B ⧸ q) ∈ (Ideal.span s).minimalPrimes`. Use `⟨⟨inferInstance, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `map_nonunit (Ideal.Quotient.mk q) _ (hx k)`.

Introduce and unpack `P ⟨hP, hsP⟩ _`. Establish `h1 : maximalIdeal B ≤ P.comap (Ideal.Quotient.mk q)`. Use `h _ (Ideal.comap_isPrime _ _) ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]`.

Conclude with `P.zero_mem`. Introduce `k`. Conclude with `hsP (Ideal.subset_span ⟨k, rfl⟩)`. Introduce `y hy`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective y`.

Apply `h1` to reduce the goal to its premises. Rewrite `hy`, the goal using `[mem_maximalIdeal]`. Conclude with `fun hu => hy (hu.map _)`. Establish `h2` using `Ideal.height_le_card_of_mem_minimalPrimes_span hs hmin`. Establish `h3 : s.ncard ≤ Nat.card κ`.

Rewrite using `[← Set.ncard_univ, show s = (fun k => Ideal.Quotient.mk q (x k)) '' Set.univ from Set.image_univ.symm]`. Conclude with `Set.ncard_image_le Set.finite_univ`. Rewrite using `[← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]`. Establish `h4 : (maximalIdeal (B ⧸ q)).height ≤ (Nat.card κ : ℕ∞)` using `h2.trans (by exact_mod_cast h3)`. Conclude with `h4` after adjusting the coercions.
-/
theorem UpperTheory.krullDim_quotient_le_card_of_radical_parameters :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (q : Ideal B) (κ : Type) [Finite κ] (x : κ → B), (∀ k, x k ∈ maximalIdeal B) → (∀ p : Ideal B, p.IsPrime → q ≤ p → (∀ k, x k ∈ p) → maximalIdeal B ≤ p) → ringKrullDim (B ⧸ q) ≤ Nat.card κ := by
  intro B _ _ _ q κ _ x hx h
  classical
  by_cases hq : q = ⊤
  · subst hq
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  haveI : Nontrivial (B ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hq
  haveI : IsLocalRing (B ⧸ q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let s : Set (B ⧸ q) := Set.range (fun k => Ideal.Quotient.mk q (x k))
  have hs : s.Finite := Set.finite_range _
  have hmin : maximalIdeal (B ⧸ q) ∈ (Ideal.span s).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      exact map_nonunit (Ideal.Quotient.mk q) _ (hx k)
    · rintro P ⟨hP, hsP⟩ _
      have h1 : maximalIdeal B ≤ P.comap (Ideal.Quotient.mk q) := by
        refine h _ (Ideal.comap_isPrime _ _) ?_ ?_
        · intro a ha
          rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
          exact P.zero_mem
        · intro k
          exact hsP (Ideal.subset_span ⟨k, rfl⟩)
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply h1
      rw [mem_maximalIdeal] at hy ⊢
      exact fun hu => hy (hu.map _)
  have h2 := Ideal.height_le_card_of_mem_minimalPrimes_span hs hmin
  have h3 : s.ncard ≤ Nat.card κ := by
    rw [← Set.ncard_univ, show s = (fun k => Ideal.Quotient.mk q (x k)) '' Set.univ from Set.image_univ.symm]
    exact Set.ncard_image_le Set.finite_univ
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have h4 : (maximalIdeal (B ⧸ q)).height ≤ (Nat.card κ : ℕ∞) := h2.trans (by exact_mod_cast h3)
  exact_mod_cast h4
