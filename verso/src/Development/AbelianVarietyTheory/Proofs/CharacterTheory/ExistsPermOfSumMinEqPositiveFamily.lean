import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory

/- English proof (translation)
Rewrite using `[Finset.card_filter, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem sum_min_succ_eq_add_card {d : ℕ} (e : Fin d → ℕ) (j : ℕ) :
    ∑ i, min (j + 1) (e i) = ∑ i, min j (e i) + (Finset.univ.filter (fun i => j < e i)).card := by
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> omega

/- English proof (translation)
Simplify using `only [Finset.card_filter]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem card_gt_eq_card_eq_add_card_gt {d : ℕ} (e : Fin d → ℕ) (j : ℕ) :
    (Finset.univ.filter (fun i => j < e i)).card =
      (Finset.univ.filter (fun i => e i = j + 1)).card +
        (Finset.univ.filter (fun i => j + 1 < e i)).card := by
  simp only [Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> omega

/- English proof (translation)
Introduce `d d' e e' he he' h`. Establish `h1 : ∀ j, (Finset.univ.filter (fun i => j < e i)).card = (Finset.univ.filter (fun i => j < e' i)).card`. Introduce `j`. Establish `a` using `sum_min_succ_eq_add_card e j`. Establish `b` using `sum_min_succ_eq_add_card e' j`.

Establish `c` using `h j`. Establish `c'` using `h (j + 1)`. Use linear arithmetic over natural numbers and integers. Establish `h2 : ∀ j, Fintype.card {i // e i = j} = Fintype.card {i // e' i = j}`. Introduce `j`.

Rewrite using `[Fintype.card_subtype, Fintype.card_subtype]`. Break down `j with _ | j` into its components or cases. Rewrite using `[Finset.filter_false_of_mem (fun i _ => (he i).ne'), Finset.filter_false_of_mem (fun i _ => (he' i).ne')]`. Simplify using the standard rewrite rules. Establish `a` using `card_gt_eq_card_eq_add_card_gt e j`.

Establish `b` using `card_gt_eq_card_eq_add_card_gt e' j`. Establish `c` using `h1 j`. Establish `c'` using `h1 (j + 1)`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨Equiv.ofFiberEquiv (f := e) (g := e') (fun j => Fintype.equivOfCardEq (h2 j)), fun i => Equiv.ofFiberEquiv_map _ i⟩`.
-/
theorem exists_equiv_of_sum_min_eq : ∀ (d d' : ℕ) (e : Fin d → ℕ) (e' : Fin d' → ℕ),
    (∀ i, 0 < e i) → (∀ i, 0 < e' i) → (∀ j : ℕ, ∑ i, min j (e i) = ∑ i, min j (e' i)) →
    ∃ σ : Fin d ≃ Fin d', ∀ i, e' (σ i) = e i := by
  intro d d' e e' he he' h
  have h1 : ∀ j, (Finset.univ.filter (fun i => j < e i)).card =
      (Finset.univ.filter (fun i => j < e' i)).card := by
    intro j
    have a := sum_min_succ_eq_add_card e j
    have b := sum_min_succ_eq_add_card e' j
    have c := h j
    have c' := h (j + 1)
    omega
  have h2 : ∀ j, Fintype.card {i // e i = j} = Fintype.card {i // e' i = j} := by
    intro j
    rw [Fintype.card_subtype, Fintype.card_subtype]
    rcases j with _ | j
    · rw [Finset.filter_false_of_mem (fun i _ => (he i).ne'),
        Finset.filter_false_of_mem (fun i _ => (he' i).ne')]
      simp
    · have a := card_gt_eq_card_eq_add_card_gt e j
      have b := card_gt_eq_card_eq_add_card_gt e' j
      have c := h1 j
      have c' := h1 (j + 1)
      omega
  exact ⟨Equiv.ofFiberEquiv (f := e) (g := e') (fun j => Fintype.equivOfCardEq (h2 j)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

end GlobalTheory
