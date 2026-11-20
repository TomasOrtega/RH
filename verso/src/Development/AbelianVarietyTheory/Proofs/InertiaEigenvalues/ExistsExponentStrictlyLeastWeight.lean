import Mathlib

open scoped BigOperators

namespace GlobalTheory

open scoped BigOperators in

/- English proof (translation)
Introduce `ρ S hS`. Establish `hwf : WellFounded (Pi.Lex (fun i j : Fin ρ => j < i) (fun {_} (x y : ℕ) => x < y))` using `Pi.Lex.wellFounded _ (fun _ => wellFounded_lt)`. Use `⟨hwf.min S hS, hwf.min_mem S hS, ?_⟩` and prove the remaining obligations. Use `set m := hwf.min S hS with hm`. Introduce `c hc a ha hne`.

Establish `hnl` using `hwf.not_lt_min S ha`. Establish `hd : (Finset.univ.filter fun i => a i ≠ m i).Nonempty`. Take `⟨i, hi⟩` from `Function.ne_iff.1 hne`. Conclude with `⟨i, by simp [hi]⟩`. Use `set k := (Finset.univ.filter fun i => a i ≠ m i).max' hd with hkdef`.

Establish `hk : a k ≠ m k` using `(Finset.mem_filter.1 (Finset.max'_mem _ hd)).2`. Establish `hgt : ∀ j, k < j → a j = m j` using `fun j hj => by`. Assume the negation of the conclusion as `h`. Conclude with `absurd (Finset.le_max' _ j (by simp [h])) (not_le.2 hj)`. Establish `hlt : m k < a k`.

Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Conclude with `absurd ⟨k, fun j hj => hgt j hj, h⟩ hnl`. Conclude with `h`. Establish `key : ∀ i, m i * c i + (if i = k then c k else 0) ≤ a i * c i + (if i < k then m i * c i else 0)`. Introduce `i`.

Break down `lt_trichotomy i k with h | h | h` into its components or cases. Simplify using `[h, h.ne]`. Substitute `h` using the available equality. Simplify using `only [if_true, lt_irrefl, if_false, add_zero]`. Use the polynomial consequences of the given equalities and inequalities.

Simplify using `[h.ne', not_lt.2 h.le, hgt i h]`. Establish `hsum` using `Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i`. Rewrite `hsum` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.sum_filter]`. Simplify using `only [Finset.mem_univ, if_true] at hsum`. Establish `hI : Finset.univ.filter (fun i => i < k) = Finset.Iio k` using `by ext; simp`.

Rewrite `hsum` using `[hI]`. Use `hc k` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem _root_.GlobalTheory.exists_exponent_strictly_least_weight :
    ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ,
      (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) →
        ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by
  intro ρ S hS
  have hwf : WellFounded (Pi.Lex (fun i j : Fin ρ => j < i) (fun {_} (x y : ℕ) => x < y)) :=
    Pi.Lex.wellFounded _ (fun _ => wellFounded_lt)
  refine ⟨hwf.min S hS, hwf.min_mem S hS, ?_⟩
  set m := hwf.min S hS with hm
  intro c hc a ha hne
  have hnl := hwf.not_lt_min S ha
  have hd : (Finset.univ.filter fun i => a i ≠ m i).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    exact ⟨i, by simp [hi]⟩
  set k := (Finset.univ.filter fun i => a i ≠ m i).max' hd with hkdef
  have hk : a k ≠ m k := (Finset.mem_filter.1 (Finset.max'_mem _ hd)).2
  have hgt : ∀ j, k < j → a j = m j := fun j hj => by
    by_contra h
    exact absurd (Finset.le_max' _ j (by simp [h])) (not_le.2 hj)
  have hlt : m k < a k := by
    rcases lt_or_gt_of_ne hk with h | h
    · exact absurd ⟨k, fun j hj => hgt j hj, h⟩ hnl
    · exact h
  have key : ∀ i, m i * c i + (if i = k then c k else 0) ≤
      a i * c i + (if i < k then m i * c i else 0) := by
    intro i
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne]
    · subst h
      simp only [if_true, lt_irrefl, if_false, add_zero]
      nlinarith
    · simp [h.ne', not_lt.2 h.le, hgt i h]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.sum_filter] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  have hI : Finset.univ.filter (fun i => i < k) = Finset.Iio k := by ext; simp
  rw [hI] at hsum
  have := hc k
  omega

end GlobalTheory
