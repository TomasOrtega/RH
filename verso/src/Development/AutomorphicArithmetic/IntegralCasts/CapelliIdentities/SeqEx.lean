import Mathlib

/- English proof (translation)
Introduce `S hfin hne t`. Use `letI : ∀ n, TopologicalSpace (S n) := fun _ => ⊥`. Use `haveI : ∀ n, DiscreteTopology (S n) := fun _ => ⟨rfl⟩`. Set `C : ℕ → Set ((n : ℕ) → S n)` to `fun k => {u | ∀ n < k, t n (u (n + 1)) = u n}`. Establish `hclosed : ∀ k, IsClosed (C k)`.

Introduce `k`. Establish `hC : C k = ⋂ n, ⋂ (_ : n < k), {u : (n : ℕ) → S n | t n (u (n + 1)) = u n}`. Use extensionality with `u`. Simplify using `[C]`. Rewrite using `[hC]`.

Use `isClosed_iInter fun n => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Conclude with `isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply (n + 1))) (continuous_apply n)`. Establish `hstep : ∀ (k : ℕ) (x : S k), ∃ u ∈ C k, u k = x`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `x`. Use `⟨Function.update (fun n => Classical.choice (hne n)) 0 x, ?_, by simp⟩` and prove the remaining obligations. Introduce `n hn`. Conclude with `absurd hn (Nat.not_lt_zero n)`.

Consider the case `succ k ih`. Introduce `x`. Take `⟨u, hu, hk⟩` from `ih (t k x)`. Use `⟨Function.update u (k + 1) x, ?_, by simp⟩` and prove the remaining obligations. Introduce `n hn`.

Break down `Nat.lt_succ_iff_lt_or_eq.mp hn with h | h` into its components or cases. Rewrite using `[Function.update_of_ne (by omega), Function.update_of_ne (by omega)]`. Conclude with `hu n h`. Substitute `h` using the available equality. Rewrite using `[Function.update_self, Function.update_of_ne (by omega), hk]`.

Establish `hnon : ∀ k, (C k).Nonempty`. Introduce `k`. Take `⟨u, hu, _⟩` from `hstep k (Classical.choice (hne k))`. Conclude with `⟨u, hu⟩`. Establish `hmono : ∀ k, C (k + 1) ⊆ C k` using `fun k u hu n hn => hu n (Nat.lt_succ_of_lt hn)`.

Take `⟨u, hu⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hmono hnon (hclosed 0).isCompact hclosed`. Conclude with `⟨u, fun n => Set.mem_iInter.mp hu (n + 1) n (Nat.lt_succ_self n)⟩`.
-/
theorem UpperTheory.Reformulated.B.Qj7.seq_ex :
    ∀ (S : ℕ → Type),
    (∀ (n : ℕ), Finite (S n)) →
      (∀ (n : ℕ), Nonempty (S n)) →
        ∀ (t : (n : ℕ) → S (n + (1 : ℕ)) → S n), ∃ (u : (n : ℕ) → S n), ∀ (n : ℕ), t n (u (n + (1 : ℕ))) = u n := by
  intro S hfin hne t
  classical
  letI : ∀ n, TopologicalSpace (S n) := fun _ => ⊥
  haveI : ∀ n, DiscreteTopology (S n) := fun _ => ⟨rfl⟩
  let C : ℕ → Set ((n : ℕ) → S n) := fun k => {u | ∀ n < k, t n (u (n + 1)) = u n}
  have hclosed : ∀ k, IsClosed (C k) := by
    intro k
    have hC : C k = ⋂ n, ⋂ (_ : n < k), {u : (n : ℕ) → S n | t n (u (n + 1)) = u n} := by
      ext u
      simp [C]
    rw [hC]
    refine isClosed_iInter fun n => isClosed_iInter fun _ => ?_
    exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply (n + 1)))
      (continuous_apply n)
  have hstep : ∀ (k : ℕ) (x : S k), ∃ u ∈ C k, u k = x := by
    intro k
    induction k with
    | zero =>
      intro x
      refine ⟨Function.update (fun n => Classical.choice (hne n)) 0 x, ?_, by simp⟩
      intro n hn
      exact absurd hn (Nat.not_lt_zero n)
    | succ k ih =>
      intro x
      obtain ⟨u, hu, hk⟩ := ih (t k x)
      refine ⟨Function.update u (k + 1) x, ?_, by simp⟩
      intro n hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h | h
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hu n h
      · subst h
        rw [Function.update_self, Function.update_of_ne (by omega), hk]
  have hnon : ∀ k, (C k).Nonempty := by
    intro k
    obtain ⟨u, hu, _⟩ := hstep k (Classical.choice (hne k))
    exact ⟨u, hu⟩
  have hmono : ∀ k, C (k + 1) ⊆ C k := fun k u hu n hn => hu n (Nat.lt_succ_of_lt hn)
  obtain ⟨u, hu⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hmono hnon
    (hclosed 0).isCompact hclosed
  exact ⟨u, fun n => Set.mem_iInter.mp hu (n + 1) n (Nat.lt_succ_self n)⟩
