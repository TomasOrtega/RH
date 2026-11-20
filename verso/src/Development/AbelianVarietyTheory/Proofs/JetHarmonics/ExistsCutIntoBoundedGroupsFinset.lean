import Mathlib

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `n hn`. Use `⟨fun _ => 0, fun _ => Nat.zero_le _, ?_, fun _ _ => rfl⟩` and prove the remaining obligations. Simplify using `only [Finset.sum_empty] at hn ⊢`.

Use linear arithmetic over natural numbers and integers. Consider the case `insert a S ha ih`. Introduce `n hn`. Rewrite `hn` using `[Finset.sum_insert ha]`. Take `⟨g, hge, hgs, hgo⟩` from `ih (min n (∑ k ∈ S, e k)) (min_le_right _ _)`.

Use `⟨fun k => if k = a then n - min n (∑ k ∈ S, e k) else g k, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Distinguish the cases in `hk : k = a`. Substitute `hk` using the available equality. Simplify using `only [if_true]`.

Use linear arithmetic over natural numbers and integers. Simplify using `only [hk, if_false]`. Conclude with `hge k`. Rewrite using `[Finset.sum_insert ha, if_pos rfl]`. Establish `hS : ∑ k ∈ S, (if k = a then n - min n (∑ k ∈ S, e k) else g k) = ∑ k ∈ S, g k`.

Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `: k ≠ a` using `fun h => ha (h ▸ hk)`. Simplify using `only [this, if_false]`. Rewrite using `[hS, hgs]`. Use linear arithmetic over natural numbers and integers.

Introduce `k hk`. Establish `hka : k ≠ a` using `fun h => hk (h ▸ Finset.mem_insert_self _ _)`. Establish `hkS : k ∉ S` using `fun h => hk (Finset.mem_insert_of_mem h)`. Simplify using `only [hka, if_false]`. Conclude with `hgo k hkS`.
-/
theorem exists_le_sum_eq_of_le_sum (S : Finset ℕ) (e : ℕ → ℕ) :
    ∀ n, n ≤ ∑ k ∈ S, e k →
      ∃ f : ℕ → ℕ, (∀ k, f k ≤ e k) ∧ ∑ k ∈ S, f k = n ∧ ∀ k, k ∉ S → f k = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro n hn
    refine ⟨fun _ => 0, fun _ => Nat.zero_le _, ?_, fun _ _ => rfl⟩
    simp only [Finset.sum_empty] at hn ⊢
    omega
  | insert a S ha ih =>
    intro n hn
    rw [Finset.sum_insert ha] at hn
    obtain ⟨g, hge, hgs, hgo⟩ := ih (min n (∑ k ∈ S, e k)) (min_le_right _ _)
    refine ⟨fun k => if k = a then n - min n (∑ k ∈ S, e k) else g k, ?_, ?_, ?_⟩
    · intro k
      by_cases hk : k = a
      · subst hk
        simp only [if_true]
        omega
      · simp only [hk, if_false]
        exact hge k
    · rw [Finset.sum_insert ha, if_pos rfl]
      have hS : ∑ k ∈ S, (if k = a then n - min n (∑ k ∈ S, e k) else g k) = ∑ k ∈ S, g k := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have : k ≠ a := fun h => ha (h ▸ hk)
        simp only [this, if_false]
      rw [hS, hgs]
      omega
    · intro k hk
      have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
      simp only [hka, if_false]
      exact hgo k hkS

/- English proof (translation)
Introduce `s`. Proceed by induction on `s with`. Consider the case `zero`. Introduce `e he`. Use `⟨fun _ _ => 0, ?_, fun u => u.elim0, fun u => u.elim0⟩` and prove the remaining obligations.

Introduce `k hk`. Simplify using `only [zero_mul, nonpos_iff_eq_zero] at he`. Rewrite `he` using `[Finset.sum_eq_zero_iff]`. Simplify using `[he k hk]`. Consider the case `succ s ih`.

Introduce `e he`. Take `⟨f, hfe, hfs, hfo⟩` from `exists_le_sum_eq_of_le_sum S e (min B (∑ k ∈ S, e k)) (min_le_right _ _)`. Establish `hsplit : ∑ k ∈ S, (e k - f k) + ∑ k ∈ S, f k = ∑ k ∈ S, e k`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (hfe k)`.

Establish `hmul : (s + 1) * B = s * B + B` using `by ring`. Take `⟨pc, hpcs, hpcb, hpco⟩` from `ih (fun k => e k - f k) (by omega)`. Use `⟨Fin.cons f pc, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k hk`. Rewrite using `[Fin.sum_univ_succ]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Rewrite using `[hpcs k hk]`. Conclude with `Nat.add_sub_cancel' (hfe k)`. Introduce `u`. Use `Fin.cases ?_ (fun i => ?_) u` and prove the remaining obligations.

Simplify using `only [Fin.cons_zero]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Fin.cons_succ]`. Conclude with `hpcb i`. Introduce `u k hk`.

Use `Fin.cases ?_ (fun i => ?_) u` and prove the remaining obligations. Simplify using `only [Fin.cons_zero]`. Conclude with `hfo k hk`. Simplify using `only [Fin.cons_succ]`. Conclude with `hpco i k hk`.
-/
theorem exists_cut_into_bounded_groups_finset (S : Finset ℕ) (B : ℕ) :
    ∀ (s : ℕ) (e : ℕ → ℕ), ∑ k ∈ S, e k ≤ s * B →
      ∃ pc : Fin s → ℕ → ℕ, (∀ k ∈ S, ∑ u, pc u k = e k) ∧ (∀ u, ∑ k ∈ S, pc u k ≤ B) ∧
        ∀ u k, k ∉ S → pc u k = 0 := by
  classical
  intro s
  induction s with
  | zero =>
    intro e he
    refine ⟨fun _ _ => 0, ?_, fun u => u.elim0, fun u => u.elim0⟩
    intro k hk
    simp only [zero_mul, nonpos_iff_eq_zero] at he
    rw [Finset.sum_eq_zero_iff] at he
    simp [he k hk]
  | succ s ih =>
    intro e he
    obtain ⟨f, hfe, hfs, hfo⟩ :=
      exists_le_sum_eq_of_le_sum S e (min B (∑ k ∈ S, e k)) (min_le_right _ _)
    have hsplit : ∑ k ∈ S, (e k - f k) + ∑ k ∈ S, f k = ∑ k ∈ S, e k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => Nat.sub_add_cancel (hfe k)
    have hmul : (s + 1) * B = s * B + B := by ring
    obtain ⟨pc, hpcs, hpcb, hpco⟩ := ih (fun k => e k - f k) (by omega)
    refine ⟨Fin.cons f pc, ?_, ?_, ?_⟩
    · intro k hk
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hpcs k hk]
      exact Nat.add_sub_cancel' (hfe k)
    · intro u
      refine Fin.cases ?_ (fun i => ?_) u
      · simp only [Fin.cons_zero]
        omega
      · simp only [Fin.cons_succ]
        exact hpcb i
    · intro u k hk
      refine Fin.cases ?_ (fun i => ?_) u
      · simp only [Fin.cons_zero]
        exact hfo k hk
      · simp only [Fin.cons_succ]
        exact hpco i k hk

/- English proof (translation)
Introduce `K s B e h`. Conclude with `exists_cut_into_bounded_groups_finset (Finset.Icc 1 K) B s e h`.
-/
theorem exists_cut_columns_bounded_width : ∀ (K s B : ℕ) (e : ℕ → ℕ), ∑ k ∈ Finset.Icc 1 K, e k ≤ s * B → ∃ pc : Fin s → ℕ → ℕ, (∀ k ∈ Finset.Icc 1 K, ∑ u, pc u k = e k) ∧ (∀ u, ∑ k ∈ Finset.Icc 1 K, pc u k ≤ B) ∧ ∀ u k, k ∉ Finset.Icc 1 K → pc u k = 0 := by
  intro K s B e h
  exact exists_cut_into_bounded_groups_finset (Finset.Icc 1 K) B s e h

end GlobalTheory
