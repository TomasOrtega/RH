import Mathlib

namespace GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid

open Finset

/- English proof (translation)
Use `choose! f hfY hf using hw`. Use `set S : Finset ℝ := (w.map f).toFinset with hS`. Establish `hSc : S.card ≤ w.length`. Combine the equalities or inequalities in the displayed calculation. Establish `hT : K * D ≤ (Y \ S).card`.

Establish `h1` using `Finset.le_card_sdiff S Y`. Generalize the expression as in `K * D = m at hcard ⊢`. Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨emb⟩ : Nonempty (Fin (K * D) ↪ ↥(Y \ S)) := by`. Rewrite using `[Function.Embedding.nonempty_iff_card_le]`.

Simplify using `using hT`. Set `φ : Fin K × Fin D ≃ Fin (K * D)` to `finProdFinEquiv`. Use `⟨fun a i => (emb (φ (a, i)) : ℝ), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a i`. Conclude with `(Finset.mem_sdiff.mp (emb (φ (a, i))).2).1`.

Introduce `a i a' i' h`. Establish `h1` using `emb.injective (Subtype.ext h)`. Establish `h2` using `φ.injective h1`. Simplify using `only [Prod.mk.injEq] at h2`. Conclude with `h2`.

Introduce `a i l hl`. Use `⟨f l, hfY l hl, ?_, hf l hl⟩` and prove the remaining obligations. Introduce `heq`. Establish `heq' : f l = (emb (φ (a, i)) : ℝ)` using `heq`. Establish `hmem` using `(Finset.mem_sdiff.mp (emb (φ (a, i))).2).2`.

Apply `hmem` to reduce the goal to its premises. Rewrite using `[← heq', hS, List.mem_toFinset, List.mem_map]`. Conclude with `⟨l, hl, rfl⟩`.
-/
theorem exists_free_family (Y : Finset ℝ) (w : List (Bool × ℝ)) (K D : ℕ)
    (hw : ∀ l ∈ w, ∃ y ∈ Y, l = (true, y) ∨ l = (false, y + 1))
    (hcard : w.length + K * D ≤ Y.card) :
    ∃ g : Fin K → Fin D → ℝ, (∀ a i, g a i ∈ Y) ∧
      (∀ a i a' i', g a i = g a' i' → a = a' ∧ i = i') ∧
      ∀ a i, ∀ l ∈ w, ∃ y ∈ Y, y ≠ g a i ∧ (l = (true, y) ∨ l = (false, y + 1)) := by
  classical
  choose! f hfY hf using hw
  set S : Finset ℝ := (w.map f).toFinset with hS
  have hSc : S.card ≤ w.length := by
    calc S.card ≤ (w.map f).length := List.toFinset_card_le _
      _ = w.length := List.length_map _
  have hT : K * D ≤ (Y \ S).card := by
    have h1 := Finset.le_card_sdiff S Y
    generalize K * D = m at hcard ⊢
    omega
  obtain ⟨emb⟩ : Nonempty (Fin (K * D) ↪ ↥(Y \ S)) := by
    rw [Function.Embedding.nonempty_iff_card_le]
    simpa using hT
  let φ : Fin K × Fin D ≃ Fin (K * D) := finProdFinEquiv
  refine ⟨fun a i => (emb (φ (a, i)) : ℝ), ?_, ?_, ?_⟩
  · intro a i
    exact (Finset.mem_sdiff.mp (emb (φ (a, i))).2).1
  · intro a i a' i' h
    have h1 := emb.injective (Subtype.ext h)
    have h2 := φ.injective h1
    simp only [Prod.mk.injEq] at h2
    exact h2
  · intro a i l hl
    refine ⟨f l, hfY l hl, ?_, hf l hl⟩
    intro heq
    have heq' : f l = (emb (φ (a, i)) : ℝ) := heq
    have hmem := (Finset.mem_sdiff.mp (emb (φ (a, i))).2).2
    apply hmem
    rw [← heq', hS, List.mem_toFinset, List.mem_map]
    exact ⟨l, hl, rfl⟩

end GroundTheory.BlockD.FourierDecayAlt.WaveGridLiftGrid
