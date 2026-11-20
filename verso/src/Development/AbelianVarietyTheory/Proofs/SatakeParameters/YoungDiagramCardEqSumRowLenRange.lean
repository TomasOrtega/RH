import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

/- English proof (translation)
Establish `hmap : ∀ c ∈ μ.cells, c.1 ∈ Finset.range n`. Introduce `c hc`. Rewrite using `[Finset.mem_range]`. Establish `h1 : (c.1, c.2) ∈ μ` using `hc`. Establish `h2 : (c.1, 0) ∈ μ` using `μ.up_left_mem le_rfl (Nat.zero_le _) h1`.

Conclude with `lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.1 h2) h`. Unfold `YoungDiagram.card`. Rewrite using `[Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (fun c hc => hmap c hc)]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[YoungDiagram.rowLen_eq_card]`.

Both sides reduce to the same expression.
-/
theorem youngDiagram_card_eq_sum_rowLen_range (μ : YoungDiagram) (n : ℕ) (h : μ.colLen 0 ≤ n) :
    μ.card = ∑ r ∈ Finset.range n, μ.rowLen r := by
  have hmap : ∀ c ∈ μ.cells, c.1 ∈ Finset.range n := by
    intro c hc
    rw [Finset.mem_range]
    have h1 : (c.1, c.2) ∈ μ := hc
    have h2 : (c.1, 0) ∈ μ := μ.up_left_mem le_rfl (Nat.zero_le _) h1
    exact lt_of_lt_of_le (YoungDiagram.mem_iff_lt_colLen.1 h2) h
  unfold YoungDiagram.card
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (fun c hc => hmap c hc)]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [YoungDiagram.rowLen_eq_card]
  rfl

/- English proof (translation)
Introduce `D hD u j hj z`. Rewrite using `[youngDiagram_card_eq_sum_rowLen_range _ _ (nuD_rows D u j z), Nat.cast_sum]`. Use `Finset.sum_congr rfl fun r hr => ?_` and prove the remaining obligations. Rewrite using `[hD u j hj z r, if_pos (Finset.mem_range.1 hr)]`.
-/
theorem nuD_card_eq_sum_nuRow : ∀ (D : D7), NuRowOK D → ∀ (u : D.what₂.Word), ∀ j < D.R.m, ∀ (z : Bool × HH D), (((nuD D u j z).card : ℕ) : ℝ) = ∑ r ∈ Finset.range (D.R.N j), DV.nuRow D u (j + 1) (tauPl D z) r := by
  intro D hD u j hj z
  rw [youngDiagram_card_eq_sum_rowLen_range _ _ (nuD_rows D u j z), Nat.cast_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [hD u j hj z r, if_pos (Finset.mem_range.1 hr)]

end GlobalTheory
