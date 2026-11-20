import Mathlib

/- English proof (translation)
Introduce `K _ r c _ _ P k hk`. Take `⟨κ, a, ha, hspan, hli⟩` from `exists_linearIndependent' K P.row`. Use `haveI : Finite κ := Finite.of_injective a ha`. Use `haveI : Fintype κ := Fintype.ofFinite κ`. Establish `hcard : Fintype.card (Fin k) ≤ Fintype.card κ`.

Rewrite using `[Fintype.card_fin, ← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row]`. Conclude with `hk`. Take `⟨e⟩` from `Function.Embedding.nonempty_of_card_le hcard`. Conclude with `⟨fun p ↦ a (e p), hli.comp e e.injective⟩`.
-/
theorem UpperTheory.Reformulated.B.Qm10.exists_rows_linearIndependent.{u, u_1, u_2} :
    ∀ {K : Type u_1} [inst : Field K] {r : Type u} {c : Type u_2} [Fintype r] [inst_2 : Fintype c]
    (P : Matrix r c K) {k : ℕ}, k ≤ P.rank → ∃ (I : Fin k → r), LinearIndependent K fun (p : Fin k) ↦ P (I p) := by
  intro K _ r c _ _ P k hk
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K P.row
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card (Fin k) ≤ Fintype.card κ := by
    rw [Fintype.card_fin, ← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row]
    exact hk
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨fun p ↦ a (e p), hli.comp e e.injective⟩
