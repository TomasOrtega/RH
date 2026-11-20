import Mathlib

open Filter Topology

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hc : ∀ j, ∃ c : ℤ, c ≠ 0 ∧ c • f j ∈ Submodule.span ℤ (Set.range e)`. Introduce `j`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Apply `hcon j` to reduce the goal to its premises. Use `LinearIndependent.finCons' (f j) e he fun c y hy hxy => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc0`. Apply `h c hc0` to reduce the goal to its premises.

Establish `: c • f j = -y` using `eq_neg_of_add_eq_zero_left hxy`. Rewrite using `[this]`. Conclude with `Submodule.neg_mem _ hy`. Use `choose c hc0 hcs using hc`. Establish `hg : LinearIndependent ℤ (fun j => c j • f j)`.

Rewrite `hf`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `a ha j`. Use `hf (fun j => a j * c j) (by simpa [mul_smul] using ha) j` as an intermediate fact. Conclude with `(mul_eq_zero.mp this).resolve_right (hc0 j)`. Establish `hle` using `linearIndependent_le_span_aux' (fun j => c j • f j) hg (Set.range e) (by rintro _ ⟨j, rfl⟩; exact hcs j)`.

Establish `h2 : Fintype.card (Set.range e) = m`. Rewrite using `[Set.card_range_of_injective he.injective, Fintype.card_fin]`. Rewrite `hle` using `[h2, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_linearIndependent_finCons_of_lt {G : Type} [AddCommGroup G] {m k : ℕ}
    (e : Fin m → G) (he : LinearIndependent ℤ e) (f : Fin k → G) (hf : LinearIndependent ℤ f)
    (hmk : m < k) : ∃ j, LinearIndependent ℤ (Fin.cons (f j) e : Fin m.succ → G) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hc : ∀ j, ∃ c : ℤ, c ≠ 0 ∧ c • f j ∈ Submodule.span ℤ (Set.range e) := by
    intro j
    by_contra h
    push_neg at h
    apply hcon j
    refine LinearIndependent.finCons' (f j) e he fun c y hy hxy => ?_
    by_contra hc0
    apply h c hc0
    have : c • f j = -y := eq_neg_of_add_eq_zero_left hxy
    rw [this]
    exact Submodule.neg_mem _ hy
  choose c hc0 hcs using hc
  have hg : LinearIndependent ℤ (fun j => c j • f j) := by
    rw [Fintype.linearIndependent_iff] at hf ⊢
    intro a ha j
    have := hf (fun j => a j * c j) (by simpa [mul_smul] using ha) j
    exact (mul_eq_zero.mp this).resolve_right (hc0 j)
  have hle := linearIndependent_le_span_aux' (fun j => c j • f j) hg (Set.range e)
    (by rintro _ ⟨j, rfl⟩; exact hcs j)
  have h2 : Fintype.card (Set.range e) = m := by
    rw [Set.card_range_of_injective he.injective, Fintype.card_fin]
  rw [h2, Fintype.card_fin] at hle
  omega

/- English proof (translation)
Introduce `k' hm`. Proceed by induction on `k', hm using Nat.le_induction with`. Consider the case `base => intro _`. Conclude with `⟨e, n, he, heS, rfl⟩`. Consider the case `succ k' hmk ih`.

Introduce `hk`. Take `⟨e2, n2, h1, h2, h3⟩` from `ih (by omega)`. Take `⟨j, hj⟩` from `exists_linearIndependent_finCons_of_lt e2 h1 f hf (by omega)`. Use `⟨Fin.cons (f j) e2, Fin.cons 0 n2, hj, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`.

Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `using hfS j`. Simplify using `using h2 i`. Rewrite using `[Fin.sum_cons, zero_add, h3]`.
-/
theorem exists_linearIndependent_extend_with_levels {G : Type} [AddCommGroup G] (S : ℕ → Set G) {k : ℕ} (f : Fin k → G)
    (hf : LinearIndependent ℤ f) (hfS : ∀ j, f j ∈ S 0) (m : ℕ) (e : Fin m → G) (n : Fin m → ℕ)
    (he : LinearIndependent ℤ e) (heS : ∀ j, e j ∈ S (n j)) :
    ∀ k', m ≤ k' → k' ≤ k → ∃ (e2 : Fin k' → G) (n2 : Fin k' → ℕ), LinearIndependent ℤ e2 ∧
      (∀ j, e2 j ∈ S (n2 j)) ∧ ∑ j, n2 j = ∑ j, n j := by
  intro k' hm
  induction k', hm using Nat.le_induction with
  | base => intro _; exact ⟨e, n, he, heS, rfl⟩
  | succ k' hmk ih =>
    intro hk
    obtain ⟨e2, n2, h1, h2, h3⟩ := ih (by omega)
    obtain ⟨j, hj⟩ := exists_linearIndependent_finCons_of_lt e2 h1 f hf (by omega)
    refine ⟨Fin.cons (f j) e2, Fin.cons 0 n2, hj, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · simpa using hfS j
      · simpa using h2 i
    · rw [Fin.sum_cons, zero_add, h3]

/- English proof (translation)
Introduce `G _ _ S hS N`. Proceed by induction on `N generalizing S with`. Consider the case `zero`. Introduce `r hr _`. Take `⟨e, he, heS⟩` from `hr 0`.

Conclude with `⟨e, fun _ => 0, he, heS, by simp⟩`. Consider the case `succ N ih`. Introduce `r hr hrd`. Take `⟨e', n', he', heS', hsum⟩` from `ih (fun i => S (i + 1)) (fun i => hS (i + 1)) (fun i => r (i + 1)) (fun i => hr (i + 1)) (fun i => hrd (i + 1))`. Take `⟨f, hf, hfS⟩` from `hr 0`.

Take `⟨e, n, he, heS, hn⟩` from `exists_linearIndependent_extend_with_levels S f hf hfS (r (0 + 1)) e' (fun j => n' j + 1) he' heS' (r 0) (hrd 0) le_rfl`. Use `⟨e, n, he, heS, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_range_succ']`. Simplify using `only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hsum hn ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_linearIndependent_adapted_to_decreasing_chain : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G]
    (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ),
    (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) →
    (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ),
      LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧
      ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by
  intro G _ _ S hS N
  induction N generalizing S with
  | zero =>
    intro r hr _
    obtain ⟨e, he, heS⟩ := hr 0
    exact ⟨e, fun _ => 0, he, heS, by simp⟩
  | succ N ih =>
    intro r hr hrd
    obtain ⟨e', n', he', heS', hsum⟩ := ih (fun i => S (i + 1)) (fun i => hS (i + 1))
      (fun i => r (i + 1)) (fun i => hr (i + 1)) (fun i => hrd (i + 1))
    obtain ⟨f, hf, hfS⟩ := hr 0
    obtain ⟨e, n, he, heS, hn⟩ := exists_linearIndependent_extend_with_levels S f hf hfS (r (0 + 1)) e' (fun j => n' j + 1) he'
      heS' (r 0) (hrd 0) le_rfl
    refine ⟨e, n, he, heS, ?_⟩
    rw [Finset.sum_range_succ']
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hsum hn ⊢
    omega

end GlobalTheory
