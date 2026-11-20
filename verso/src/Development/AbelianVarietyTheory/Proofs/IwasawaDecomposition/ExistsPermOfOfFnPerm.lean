import Mathlib

namespace GlobalTheory.FiberCardPermutation

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the equality to equality of the corresponding arguments. A detailed English derivation is pending.
-/
theorem card_fiber_eq_count {α : Type} [DecidableEq α] {n : ℕ} (v : Fin n → α) (c : α) :
    Fintype.card {i : Fin n // v i = c} = Multiset.count c (List.ofFn v : Multiset α) := by
  rw [← Fin.univ_val_map, Multiset.count_map, Fintype.card_subtype]
  simp only [Finset.card, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun _ _ => eq_comm)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Reduce the conclusion to the remaining proof obligations. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem exists_perm_of_ofFn_perm {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : List.Perm (List.ofFn v) (List.ofFn w)) :
    ∃ σ : Equiv.Perm (Fin n), v = w ∘ (⇑σ : Fin n → Fin n) := by
  classical
  have hm : (List.ofFn v : Multiset α) = (List.ofFn w : Multiset α) := Multiset.coe_eq_coe.mpr h
  have hc : ∀ c : α, Fintype.card {i : Fin n // v i = c} = Fintype.card {i : Fin n // w i = c} := by
    intro c
    have h1 := card_fiber_eq_count v c
    have h2 := card_fiber_eq_count w c
    rw [hm, ← h2] at h1
    convert h1
  refine ⟨Equiv.ofFiberEquiv (f := v) (g := w) (fun c => Fintype.equivOfCardEq (hc c)), ?_⟩
  funext i
  exact (Equiv.ofFiberEquiv_map (f := v) (g := w) _ i).symm

end GlobalTheory.FiberCardPermutation
