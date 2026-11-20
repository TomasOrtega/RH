import Mathlib

namespace PeriodicSumRangeMul

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[show (k + 1) * P + x = (k * P + x) + P by ring, h, ih]`.
-/
private lemma per {N : Type} [AddCommGroup N] (g : ℕ → N) (P : ℕ)
    (h : ∀ (i : ℕ), g (i + P) = g i) (k x : ℕ) : g (k * P + x) = g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P + x = (k * P + x) + P by ring, h, ih]

end PeriodicSumRangeMul

/- English proof (translation)
Introduce `N _ g P h k`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[show (k + 1) * P = k * P + P by ring, Finset.sum_range_add, ih, succ_nsmul]`.

Use `congr 1`. Conclude with `Finset.sum_congr rfl (fun x _ => PeriodicSumRangeMul.per g P h k x)`.
-/
theorem UpperTheory.Reformulated.B.Yra7.main :
    ∀ {N : Type} [inst : AddCommGroup N] (g : ℕ → N) (P : ℕ),
      (∀ (i : ℕ), g (i + P) = g i) → ∀ (k : ℕ), ∑ i ∈ Finset.range (k * P), g i = k • ∑ i ∈ Finset.range P, g i := by
  intro N _ g P h k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (k + 1) * P = k * P + P by ring, Finset.sum_range_add, ih, succ_nsmul]
    congr 1
    exact Finset.sum_congr rfl (fun x _ => PeriodicSumRangeMul.per g P h k x)
