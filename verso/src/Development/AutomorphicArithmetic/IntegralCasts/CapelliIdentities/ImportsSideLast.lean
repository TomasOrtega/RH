import Mathlib

/- English proof (translation)
Introduce `n z z' h`. Establish `key : ∀ (w : Fin n → ℂˣ) (c : ℂ), Fintype.card {i : Fin n // (w i : ℂ) = c} = Multiset.count c (Multiset.map (fun (i : Fin n) ↦ (↑(w i) : ℂ)) Finset.univ.val)`. Introduce `w c`. Rewrite using `[Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]`. Use `congr 1`.

Conclude with `Multiset.filter_congr (fun _ _ => eq_comm)`. Establish `hc : ∀ c : ℂ, Fintype.card {i : Fin n // (z' i : ℂ) = c} = Fintype.card {i : Fin n // (z i : ℂ) = c}`. Introduce `c`. Rewrite using `[key, key, h]`. Set `e : ∀ c : ℂ, {i : Fin n // (z' i : ℂ) = c} ≃ {i : Fin n // (z i : ℂ) = c}` to `fun c => Fintype.equivOfCardEq (hc c)`.

Use `⟨Equiv.ofFiberEquiv (f := fun i => (z' i : ℂ)) (g := fun i => (z i : ℂ)) e, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `(Equiv.ofFiberEquiv_map (f := fun i => (z' i : ℂ)) (g := fun i => (z i : ℂ)) e i).symm`.
-/
theorem UpperTheory.Reformulated.B.Yoa3.exists_perm_of_map_eq :
    ∀ {n : ℕ} {z z' : Fin n → ℂˣ},
      Multiset.map (fun (i : Fin n) ↦ (↑(z i) : ℂ)) Finset.univ.val =
          Multiset.map (fun (i : Fin n) ↦ (↑(z' i) : ℂ)) Finset.univ.val →
        ∃ (σ : Equiv.Perm (Fin n)), z' = z ∘ (⇑σ : Fin n → Fin n) := by
  classical
  intro n z z' h
  have key : ∀ (w : Fin n → ℂˣ) (c : ℂ),
      Fintype.card {i : Fin n // (w i : ℂ) = c} =
        Multiset.count c (Multiset.map (fun (i : Fin n) ↦ (↑(w i) : ℂ)) Finset.univ.val) := by
    intro w c
    rw [Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun _ _ => eq_comm)
  have hc : ∀ c : ℂ, Fintype.card {i : Fin n // (z' i : ℂ) = c} =
      Fintype.card {i : Fin n // (z i : ℂ) = c} := by
    intro c
    rw [key, key, h]
  let e : ∀ c : ℂ, {i : Fin n // (z' i : ℂ) = c} ≃ {i : Fin n // (z i : ℂ) = c} :=
    fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv (f := fun i => (z' i : ℂ)) (g := fun i => (z i : ℂ)) e, ?_⟩
  funext i
  apply Units.ext
  exact (Equiv.ofFiberEquiv_map (f := fun i => (z' i : ℂ)) (g := fun i => (z i : ℂ)) e i).symm
