import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `M N _ _ e B h`. Take `⟨hfin, hcard⟩` from `h`. Set `f : AddCommGroup.torsion M ≃ AddCommGroup.torsion N` to `(e : M ≃ N).subtypeEquiv fun x => by`. Simplify using `only [SetLike.mem_coe, AddCommGroup.mem_torsion, ← addOrderOf_pos_iff]`.

Simplify using the standard rewrite rules. Conclude with `⟨Finite.of_equiv _ f, (Nat.card_congr f).symm ▸ hcard⟩`. Introduce `M N e B h`. Take `⟨hfin, hcard⟩` from `h`. Conclude with `⟨Finite.of_equiv _ e, (Nat.card_congr e).symm ▸ hcard⟩`.

Introduce `M _ B B' hB h`. Conclude with `⟨h.1, h.2.trans hB⟩`. Introduce `M B B' hB h`. Conclude with `⟨h.1, h.2.trans hB⟩`.
-/
theorem UpperTheory.V.KH.transport :
    (∀ (M N : Type) [AddCommGroup M] [AddCommGroup N] (_ : M ≃+ N) (B : ℕ), TorsLe M B → TorsLe N B) ∧
    (∀ (M N : Type) (_ : M ≃ N) (B : ℕ), CardLe M B → CardLe N B) ∧
    (∀ (M : Type) [AddCommGroup M] (B B' : ℕ), B ≤ B' → TorsLe M B → TorsLe M B') ∧
    (∀ (M : Type) (B B' : ℕ), B ≤ B' → CardLe M B → CardLe M B') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M N _ _ e B h
    obtain ⟨hfin, hcard⟩ := h
    let f : AddCommGroup.torsion M ≃ AddCommGroup.torsion N :=
      (e : M ≃ N).subtypeEquiv fun x => by
        simp only [SetLike.mem_coe, AddCommGroup.mem_torsion, ← addOrderOf_pos_iff]
        simp
    exact ⟨Finite.of_equiv _ f, (Nat.card_congr f).symm ▸ hcard⟩
  · intro M N e B h
    obtain ⟨hfin, hcard⟩ := h
    exact ⟨Finite.of_equiv _ e, (Nat.card_congr e).symm ▸ hcard⟩
  · intro M _ B B' hB h
    exact ⟨h.1, h.2.trans hB⟩
  · intro M B B' hB h
    exact ⟨h.1, h.2.trans hB⟩
