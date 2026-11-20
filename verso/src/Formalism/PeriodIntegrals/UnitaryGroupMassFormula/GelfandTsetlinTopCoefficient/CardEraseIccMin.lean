import Mathlib

namespace PI.GTNum

open Finset

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[sum_range_succ]`. Establish `h1` using `ih (fun i hi => h i (by omega))`.

Establish `h2` using `h n (by omega)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_range_le_tele (n : ℕ) (a t : ℕ → ℤ) (h : ∀ i < n, a i ≤ t i - t (i + 1)) :
    ∑ i ∈ range n, a i ≤ t 0 - t n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have h1 := ih (fun i hi => h i (by omega))
    have h2 := h n (by omega)
    linarith

/- English proof (translation)
Rewrite using `[Finset.card_erase_of_mem hx, Int.card_Icc]`. Establish `h1 : 1 ≤ (min b (a + c) + 1 - a).toNat` using `by omega`. Rewrite using `[Nat.cast_sub h1, Int.toNat_of_nonneg (by omega)]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_erase_Icc_min (a b c x : ℤ) (hab : a ≤ b) (hc : 0 ≤ c)
    (hx : x ∈ Icc a (min b (a + c))) :
    ((((Icc a (min b (a + c))).erase x).card : ℕ) : ℤ) = min (b - a) c := by
  rw [Finset.card_erase_of_mem hx, Int.card_Icc]
  have h1 : 1 ≤ (min b (a + c) + 1 - a).toNat := by omega
  rw [Nat.cast_sub h1, Int.toNat_of_nonneg (by omega)]
  push_cast
  omega

/- English proof (translation)
The claim follows from `|∏ x ∈ s, f x| ≤ ∏ x ∈ s, b x := by rw [abs_prod] exact Finset.prod_le_prod (fun x _ => abs_nonneg _) h`.
-/
theorem abs_prod_le_prod {α : Type*} (s : Finset α) (f b : α → ℤ) (h : ∀ x ∈ s, |f x| ≤ b x) :
    |∏ x ∈ s, f x| ≤ ∏ x ∈ s, b x := by
  rw [abs_prod]
  exact Finset.prod_le_prod (fun x _ => abs_nonneg _) h

/- English proof (translation)
The claim follows from `|∏ x ∈ s, f x| ≤ B ^ s.card := by simpa [Finset.prod_const] using abs_prod_le_prod s f (fun _ => B) h`.
-/
theorem abs_prod_le_pow {α : Type*} (s : Finset α) (f : α → ℤ) (B : ℤ) (h : ∀ x ∈ s, |f x| ≤ B) :
    |∏ x ∈ s, f x| ≤ B ^ s.card := by
  simpa [Finset.prod_const] using abs_prod_le_prod s f (fun _ => B) h

/- English proof (translation)
Rewrite using `[Finset.prod_pow_eq_pow_sum, ← pow_mul]`.
-/
theorem prod_pow_pow {α : Type*} (s : Finset α) (B : ℤ) (m : ℕ) (e : α → ℕ) :
    ∏ x ∈ s, (B ^ m) ^ e x = B ^ (m * ∑ x ∈ s, e x) := by
  rw [Finset.prod_pow_eq_pow_sum, ← pow_mul]

/- English proof (translation)
The claim follows from `|v - (i : ℤ) - s + (j : ℤ)| ≤ 2 * (S - L) + ((n + 1 : ℕ) : ℤ) := by rw [abs_le] push_cast constructor <;> omega`.
-/
theorem abs_factor_le (v s L S : ℤ) (i j n : ℕ) (hi : i < n) (hj : j < n)
    (hv1 : L ≤ v) (hv2 : v ≤ S + (S - L)) (hs1 : L ≤ s) (hs2 : s ≤ S) :
    |v - (i : ℤ) - s + (j : ℤ)| ≤ 2 * (S - L) + ((n + 1 : ℕ) : ℤ) := by
  rw [abs_le]
  push_cast
  constructor <;> omega

end PI.GTNum
