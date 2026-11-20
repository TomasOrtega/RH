import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

/- English proof (translation)
Introduce `m lam hlam T hT t i j hij`. Establish `hmem : ∀ p : youngCells lam, p.1.1 = j → (i, p.1.2) ∈ youngCells lam`. Introduce `p hp`. Establish `hp'` using `p.2`. Simplify using `only [youngCells, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_range] at hp' ⊢`.

Establish `h1 : p.1.2 < lam i`. Rewrite `hp'` using `[hp]`. Conclude with `lt_of_lt_of_le hp'.2 (hlam hij)`. Use `⟨lt_of_lt_of_le h1 ?_, h1⟩` and prove the remaining obligations. Conclude with `Finset.single_le_sum (fun k _ => Nat.zero_le (lam k)) (Finset.mem_univ i)`.

Set `f : youngCells lam → youngCells lam` to `fun p => if h : p.1.1 = j then ⟨(i, p.1.2), hmem p h⟩ else p`. Establish `hf : ∀ p : youngCells lam, ∀ h : p.1.1 = j, f p = ⟨(i, p.1.2), hmem p h⟩`. Introduce `p h`. Simplify using `only [f, dif_pos h]`. Apply `Finset.card_le_card_of_injOn f` to reduce the goal to its premises.

Introduce `p hp`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢`. Rewrite using `[hf p hp.1]`. Use `⟨rfl, lt_of_le_of_lt ?_ hp.2⟩` and prove the remaining obligations. Use `hT ⟨(i, p.1.2), hmem p hp.1⟩ p (by simpa [hp.1] using hij) le_rfl` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Introduce `p hp q hq hpq`. Simplify using `only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq`. Rewrite `hpq` using `[hf p hp.1, hf q hq.1]`. Establish `h2 : p.1.2 = q.1.2`.

Use `congrArg (fun x : youngCells lam => x.1.2) hpq` as an intermediate fact. Simplify using `using this`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `Prod.ext (hp.1.trans hq.1.symm) h2`.
-/
theorem CombTableauRowLattice.proof : CombTableauRowLattice.Statement := by
  classical
  intro m lam hlam T hT t i j hij
  have hmem : ∀ p : youngCells lam, p.1.1 = j → (i, p.1.2) ∈ youngCells lam := by
    intro p hp
    have hp' := p.2
    simp only [youngCells, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_range] at hp' ⊢
    have h1 : p.1.2 < lam i := by
      rw [hp] at hp'
      exact lt_of_lt_of_le hp'.2 (hlam hij)
    refine ⟨lt_of_lt_of_le h1 ?_, h1⟩
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (lam k)) (Finset.mem_univ i)
  let f : youngCells lam → youngCells lam := fun p =>
    if h : p.1.1 = j then ⟨(i, p.1.2), hmem p h⟩ else p
  have hf : ∀ p : youngCells lam, ∀ h : p.1.1 = j, f p = ⟨(i, p.1.2), hmem p h⟩ := by
    intro p h
    simp only [f, dif_pos h]
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
    rw [hf p hp.1]
    refine ⟨rfl, lt_of_le_of_lt ?_ hp.2⟩
    have := hT ⟨(i, p.1.2), hmem p hp.1⟩ p (by simpa [hp.1] using hij) le_rfl
    exact_mod_cast this
  · intro p hp q hq hpq
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
    rw [hf p hp.1, hf q hq.1] at hpq
    have h2 : p.1.2 = q.1.2 := by
      have := congrArg (fun x : youngCells lam => x.1.2) hpq
      simpa using this
    apply Subtype.ext
    exact Prod.ext (hp.1.trans hq.1.symm) h2

end GroundTheory.Heights₂.Heights.RestTerms
