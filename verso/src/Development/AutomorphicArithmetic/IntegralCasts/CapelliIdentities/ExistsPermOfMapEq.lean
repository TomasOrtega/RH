import Mathlib

/- English proof (translation)
Introduce `n a b h`. Establish `key : ∀ (f : Fin n → ℂ) (c : ℂ), Fintype.card {i // f i = c} = Multiset.count c (Multiset.map f Finset.univ.val)`. Introduce `f c`. Rewrite using `[Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]`. Use `congr 1`.

Conclude with `Multiset.filter_congr (fun _ _ => eq_comm)`. Establish `hc : ∀ c : ℂ, Fintype.card {i // a i = c} = Fintype.card {i // b i = c}`. Introduce `c`. Rewrite using `[key a c, key b c, h]`. Conclude with `⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)), fun i => Equiv.ofFiberEquiv_map _ i⟩`.
-/
theorem UpperTheory.Reformulated.B.Qh57.exists_perm_of_map_eq :
    ∀ {n : ℕ} (a b : Fin n → ℂ),
    Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val →
      ∃ (e : Equiv.Perm (Fin n)), ∀ (i : Fin n), b ((e : Fin n → Fin n) i) = a i := by
  intro n a b h
  classical
  have key : ∀ (f : Fin n → ℂ) (c : ℂ),
      Fintype.card {i // f i = c} = Multiset.count c (Multiset.map f Finset.univ.val) := by
    intro f c
    rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun _ _ => eq_comm)
  have hc : ∀ c : ℂ, Fintype.card {i // a i = c} = Fintype.card {i // b i = c} := by
    intro c
    rw [key a c, key b c, h]
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩
