import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset

/- English proof (translation)
Set `t : Finset (Fin m ×ₗ ℕ)` to `(youngCells lam).map (toLex : Fin m × ℕ ≃ _).toEmbedding`. Establish `ht : t.card = (youngCells lam).card` using `Finset.card_map _`. Set `e : Fin (youngCells lam).card ≃o t` to `t.orderIsoOfFin ht`. Set `g : youngCells lam ≃ t` to `Equiv.subtypeEquiv toLex fun p => by simp [t]`. Set `T : youngCells lam ≃ Fin (youngCells lam).card` to `g.trans e.symm.toEquiv`.

Establish `hT : ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q`. Introduce `p q h1 h2`. Apply `e.symm.monotone` to reduce the goal to its premises. Use `show toLex p.1 ≤ toLex q.1`. Conclude with `Prod.Lex.toLex_mono ⟨h1, h2⟩`.

Establish `: Nonempty {T : youngCells lam ≃ Fin (youngCells lam).card // ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q}` using `⟨⟨T, hT⟩⟩`. Conclude with `Nat.card_pos`.
-/
theorem numStandardTable_pos {m : ℕ} (lam : Fin m → ℕ) : 0 < numStandardTable lam := by
  classical
  let t : Finset (Fin m ×ₗ ℕ) := (youngCells lam).map (toLex : Fin m × ℕ ≃ _).toEmbedding
  have ht : t.card = (youngCells lam).card := Finset.card_map _
  let e : Fin (youngCells lam).card ≃o t := t.orderIsoOfFin ht
  let g : youngCells lam ≃ t :=
    Equiv.subtypeEquiv toLex fun p => by simp [t]
  let T : youngCells lam ≃ Fin (youngCells lam).card := g.trans e.symm.toEquiv
  have hT : ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q := by
    intro p q h1 h2
    apply e.symm.monotone
    show toLex p.1 ≤ toLex q.1
    exact Prod.Lex.toLex_mono ⟨h1, h2⟩
  have : Nonempty {T : youngCells lam ≃ Fin (youngCells lam).card //
      ∀ p q : youngCells lam, p.1.1 ≤ q.1.1 → p.1.2 ≤ q.1.2 → T p ≤ T q} := ⟨⟨T, hT⟩⟩
  exact Nat.card_pos

/- English proof (translation)
Introduce `r a` and use `numStandardTable_pos (rectangle r a)`.
-/
theorem RectangleTablePos.intersectionNumber_baseChange : RectangleTablePos.Statement :=
  fun r a => numStandardTable_pos (rectangle r a)

/- English proof (translation)
The claim follows from `RectangleTablePos.intersectionNumber_baseChange`.
-/
theorem RectangleTablePos.proof (_h : FrobeniusDimensionFormula.Statement) :
    RectangleTablePos.Statement :=
  RectangleTablePos.intersectionNumber_baseChange

end GroundTheory.Heights₂.Heights.RestTerms
