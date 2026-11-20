import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.TwSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.FerreroWashingtonIndex.GcDiff

open UpperTheory.V.FW

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `h` using `gcDiff M c (s - ((c * n : ℕ) : ZMod M)) hc`. Establish `e : s - ((c * (n + 1) : ℕ) : ZMod M) = s - ((c * n : ℕ) : ZMod M) - c` using `by push_cast; ring`.

Rewrite using `[e, Nat.mul_succ, Finset.sum_range_add, ← ih]`. Establish `key : (∑ j ∈ Finset.range c, if ((c * n + j : ℕ) : ZMod M) = s then (1 - if c ∣ c * n + j then (c : ℤ) else 0) else 0) = (∑ j ∈ Finset.range c, if (j : ZMod M) = s - ((c * n : ℕ) : ZMod M) then 1 else 0) - if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0`. Break down `Nat.eq_zero_or_pos c with rfl | hpos` into its components or cases. Simplify using the standard rewrite rules. Establish `h2 : (if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0) = ∑ j ∈ Finset.range c, if j = 0 then (if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0) else 0`.

Rewrite using `[Finset.sum_ite_eq' (Finset.range c) 0]`. Simplify using `[hpos]`. Rewrite using `[h2, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj'` using `Finset.mem_range.1 hj`.

Establish `h3 : (((c * n + j : ℕ) : ZMod M) = s) ↔ (j : ZMod M) = s - ((c * n : ℕ) : ZMod M)`. Rewrite using `[Nat.cast_add, eq_sub_iff_add_eq']`. Establish `h4 : c ∣ c * n + j ↔ j = 0`. Rewrite using `[Nat.dvd_add_right (dvd_mul_right c n)]`. Conclude with `⟨fun h => Nat.eq_zero_of_dvd_of_lt h hj', fun h => h ▸ dvd_zero c⟩`.

Simplify using `only [h3, h4]`. Generalize the expression as in `s - ((c * n : ℕ) : ZMod M) = t`. Distinguish the cases in `h0 : j = 0`. Substitute `h0` using the available equality. Distinguish the cases in `ht : t = 0`.

Simplify using `[ht]`. Simplify using `[ht, Ne.symm ht]`. Simplify using `[h0]`. Rewrite using `[key, ← h]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem gauss_count_shift_eq_sum (M c : ℕ) [NeZero M] (s : ZMod M) (hc : c.Coprime M) (n : ℕ) :
    gc M c s - gc M c (s - ((c * n : ℕ) : ZMod M)) =
      ∑ j ∈ Finset.range (c * n), if (j : ZMod M) = s then (1 - if c ∣ j then (c : ℤ) else 0) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := gcDiff M c (s - ((c * n : ℕ) : ZMod M)) hc
    have e : s - ((c * (n + 1) : ℕ) : ZMod M) = s - ((c * n : ℕ) : ZMod M) - c := by
      push_cast; ring
    rw [e, Nat.mul_succ, Finset.sum_range_add, ← ih]
    have key : (∑ j ∈ Finset.range c, if ((c * n + j : ℕ) : ZMod M) = s then
        (1 - if c ∣ c * n + j then (c : ℤ) else 0) else 0) =
        (∑ j ∈ Finset.range c, if (j : ZMod M) = s - ((c * n : ℕ) : ZMod M) then 1 else 0) -
          if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0 := by
      rcases Nat.eq_zero_or_pos c with rfl | hpos
      · simp
      have h2 : (if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0) =
          ∑ j ∈ Finset.range c, if j = 0 then
            (if s - ((c * n : ℕ) : ZMod M) = 0 then (c : ℤ) else 0) else 0 := by
        rw [Finset.sum_ite_eq' (Finset.range c) 0]
        simp [hpos]
      rw [h2, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' := Finset.mem_range.1 hj
      have h3 : (((c * n + j : ℕ) : ZMod M) = s) ↔ (j : ZMod M) = s - ((c * n : ℕ) : ZMod M) := by
        rw [Nat.cast_add, eq_sub_iff_add_eq']
      have h4 : c ∣ c * n + j ↔ j = 0 := by
        rw [Nat.dvd_add_right (dvd_mul_right c n)]
        exact ⟨fun h => Nat.eq_zero_of_dvd_of_lt h hj', fun h => h ▸ dvd_zero c⟩
      simp only [h3, h4]
      generalize s - ((c * n : ℕ) : ZMod M) = t
      by_cases h0 : j = 0
      · subst h0
        by_cases ht : t = 0
        · simp [ht]
        · simp [ht, Ne.symm ht]
      · simp [h0]
    rw [key, ← h]
    ring

/- English proof (translation)
Introduce `M c F _ k _ Ψ s hc hΨ`. Establish `hp : ∀ n : ℕ, Ψ (s - ((n * F : ℕ) : ZMod M)) = Ψ s`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ n ih`. Rewrite using `[← ih, ← hΨ (s - (((n + 1) * F : ℕ) : ZMod M))]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hp c, ← sub_mul, ← Int.cast_sub, gauss_count_shift_eq_sum M c s hc F, Int.cast_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : (j : ZMod M) = s`. Rewrite using `[if_pos h, if_pos h, h, mul_comm]`. Apply the tactic sequence `by_cases h' : c ∣ j <;> simp [h']`.

Simplify using `[h]`.
-/
theorem UpperTheory.V.FW.gcShift :
    ∀ (M c F : ℕ) [NeZero M] (k : Type) [CommRing k] (Ψ : ZMod M → k) (s : ZMod M), c.Coprime M → (∀ x, Ψ (x + F) = Ψ x) → (gc M c s : k) * Ψ s - (gc M c (s - ((c * F : ℕ) : ZMod M)) : k) * Ψ (s - ((c * F : ℕ) : ZMod M)) = ∑ j ∈ Finset.range (c * F), if (j : ZMod M) = s then Ψ j * (1 - if c ∣ j then (c : k) else 0) else 0 := by
  intro M c F _ k _ Ψ s hc hΨ
  have hp : ∀ n : ℕ, Ψ (s - ((n * F : ℕ) : ZMod M)) = Ψ s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih, ← hΨ (s - (((n + 1) * F : ℕ) : ZMod M))]
      congr 1
      push_cast; ring
  rw [hp c, ← sub_mul, ← Int.cast_sub, gauss_count_shift_eq_sum M c s hc F, Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : (j : ZMod M) = s
  · rw [if_pos h, if_pos h, h, mul_comm]
    by_cases h' : c ∣ j <;> simp [h']
  · simp [h]
