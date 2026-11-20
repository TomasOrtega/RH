import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL Finset

namespace GlobalTheory

/- English proof (translation)
Establish `hT : ∀ (v : ℂ) (c : Fin n) (i : Fin t), Commute (Tm E v c (b i)) x`. Introduce `v c i`. Establish `h1 : Commute (E c (b i)) x` using `h c i`. Unfold `Tm`. Use `Commute.add_left ?_ h1` and prove the remaining obligations.

Use `split_ifs`. Conclude with `Algebra.commutes v x`. Conclude with `Commute.zero_left x`. Express the relevant statement in the definitionally equal form `Commute (qminor E a b u) x`. Unfold `qminor`.

Use `Commute.sum_left _ _ _ fun σ _ => ?_` and prove the remaining obligations. Establish `hp : ∀ f : Fin t → A, (∀ i, Commute (f i) x) → Commute (List.ofFn f).prod x`. Introduce `f hf`. Use `Commute.list_prod_left _ _ fun y hy => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `List.mem_ofFn.1 hy`.

Conclude with `hf i`. Conclude with `(Int.cast_commute _ x).mul_left (hp _ fun i => hT _ _ i)`.
-/
theorem qminor_comm_of_comm_columns (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ)
    (E : Fin n → Fin n → A) (x : A) (a b : Fin t → Fin n) (u : ℂ)
    (h : ∀ (c : Fin n) (i : Fin t), E c (b i) * x = x * E c (b i)) :
    qminor E a b u * x = x * qminor E a b u := by
  have hT : ∀ (v : ℂ) (c : Fin n) (i : Fin t), Commute (Tm E v c (b i)) x := by
    intro v c i
    have h1 : Commute (E c (b i)) x := h c i
    unfold Tm
    refine Commute.add_left ?_ h1
    split_ifs
    · exact Algebra.commutes v x
    · exact Commute.zero_left x
  change Commute (qminor E a b u) x
  unfold qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  have hp : ∀ f : Fin t → A, (∀ i, Commute (f i) x) → Commute (List.ofFn f).prod x := by
    intro f hf
    refine Commute.list_prod_left _ _ fun y hy => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hy
    exact hf i
  exact (Int.cast_commute _ x).mul_left (hp _ fun i => hT _ _ i)

end GlobalTheory
