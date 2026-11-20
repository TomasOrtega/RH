import Mathlib

namespace ListOfFnPermExistsEquivPerm

open Finset in
/- English proof (translation)
The claim follows from `| 0, v, a => by simp | n + 1, v, a => by have ih := card_count (fun i : Fin n => v i.succ) a rw [Fin.card_filter_univ_succ', List.ofFn_succ, List.count_cons, ih] by_cases h : v 0 = a <;> simp [h, add_comm]`.
-/
private theorem card_count {α : Type} [DecidableEq α] :
    ∀ {n : ℕ} (v : Fin n → α) (a : α), #{i | v i = a} = (List.ofFn v).count a
  | 0, v, a => by simp
  | n + 1, v, a => by
    have ih := card_count (fun i : Fin n => v i.succ) a
    rw [Fin.card_filter_univ_succ', List.ofFn_succ, List.count_cons, ih]
    by_cases h : v 0 = a <;> simp [h, add_comm]

end ListOfFnPermExistsEquivPerm

/- English proof (translation)
Introduce `α n v w h`. Establish `hc : ∀ c, Fintype.card {i // v i = c} = Fintype.card {i // w i = c}`. Introduce `c`. Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`. Use `(ListOfFnPermExistsEquivPerm.card_count v c).trans ((h.count_eq c).trans (ListOfFnPermExistsEquivPerm.card_count w c).symm)` and compare the differences between its conclusion and the goal.

Use `⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Conclude with `(Equiv.ofFiberEquiv_map _ i).symm`.
-/
theorem UpperTheory.Reformulated.B.Yde7.main :
    ∀ {α : Type} {n : ℕ} (v w : Fin n → α),
      (List.ofFn v).Perm (List.ofFn w) → ∃ (s : Equiv.Perm (Fin n)), v = w ∘ (⇑s : Fin n → Fin n) := by
  intro α n v w h
  classical
  have hc : ∀ c, Fintype.card {i // v i = c} = Fintype.card {i // w i = c} := by
    intro c
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert (ListOfFnPermExistsEquivPerm.card_count v c).trans ((h.count_eq c).trans (ListOfFnPermExistsEquivPerm.card_count w c).symm)
  refine ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map _ i).symm
