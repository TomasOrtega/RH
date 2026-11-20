import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubledFlagSumEqUnipotentDimAndLayerProd

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadicalDimSum

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on_max with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih`. Establish `hna : a ∉ s` using `fun h => lt_irrefl a (ha a h)`. Establish `h2 : (insert a s).filter (fun k => a < k) = ∅`.

Apply `Finset.filter_eq_empty_iff.mpr` to reduce the goal to its premises. Introduce `x hx`. Break down `Finset.mem_insert.mp hx with rfl | hx` into its components or cases. Conclude with `lt_irrefl _`. Conclude with `not_lt.mpr (ha x hx).le`.

Establish `h3 : ∑ i ∈ s, ∑ k ∈ (insert a s).filter (fun k => i < k), f i * f k = ∑ i ∈ s, ∑ k ∈ s.filter (fun k => i < k), f i * f k + (∑ i ∈ s, f i) * f a`. Rewrite using `[Finset.sum_mul, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun i hi => ?_)` and prove the remaining obligations. Rewrite using `[Finset.filter_insert, if_pos (ha i hi), Finset.sum_insert (by simp [hna])]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [Finset.sum_insert hna]`. Rewrite using `[h2, Finset.sum_empty, h3, show (f a + ∑ i ∈ s, f i) ^ 2 = f a ^ 2 + 2 * (∑ i ∈ s, f i) * f a + (∑ i ∈ s, f i) ^ 2 by ring, ← ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem two_mul_pairs_add_sq {ι : Type} [LinearOrder ι] (s : Finset ι) (f : ι → ℕ) :
    2 * (∑ i ∈ s, ∑ k ∈ s.filter (fun k => i < k), f i * f k) + ∑ i ∈ s, f i ^ 2 = (∑ i ∈ s, f i) ^ 2 := by
  classical
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hna : a ∉ s := fun h => lt_irrefl a (ha a h)
    have h2 : (insert a s).filter (fun k => a < k) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact lt_irrefl _
      · exact not_lt.mpr (ha x hx).le
    have h3 : ∑ i ∈ s, ∑ k ∈ (insert a s).filter (fun k => i < k), f i * f k
        = ∑ i ∈ s, ∑ k ∈ s.filter (fun k => i < k), f i * f k + (∑ i ∈ s, f i) * f a := by
      rw [Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      rw [Finset.filter_insert, if_pos (ha i hi), Finset.sum_insert (by simp [hna])]
      ring
    simp only [Finset.sum_insert hna]
    rw [h2, Finset.sum_empty, h3,
      show (f a + ∑ i ∈ s, f i) ^ 2 = f a ^ 2 + 2 * (∑ i ∈ s, f i) * f a + (∑ i ∈ s, f i) ^ 2 by ring,
      ← ih]
    ring

/- English proof (translation)
Establish `e : ∑ c ∈ range N, r (b + c + 1) = ∑ k ∈ Ico (b + 1) (b + 1 + N), r k`. Rewrite using `[Finset.sum_Ico_eq_sum_range, show b + 1 + N - (b + 1) = N by omega]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[e]`. Use `symm`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `k hk`. Simplify using `only [Finset.mem_filter, Finset.mem_range] at hk`.

Simplify using `only [Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Introduce `k hk hk'`. Simplify using `only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_and, not_lt] at hk hk'`. Apply `hr` to reduce the goal to its premises.

Assume the negation of the conclusion as `h`. Conclude with `absurd (hk' (by omega)) (by omega)`.
-/
theorem sum_shift_eq (N : ℕ) (r : ℕ → ℕ) (hr : ∀ b, N ≤ b → r b = 0) (b : ℕ) :
    ∑ c ∈ range N, r (b + c + 1) = ∑ k ∈ (range N).filter (fun k => b < k), r k := by
  have e : ∑ c ∈ range N, r (b + c + 1) = ∑ k ∈ Ico (b + 1) (b + 1 + N), r k := by
    rw [Finset.sum_Ico_eq_sum_range, show b + 1 + N - (b + 1) = N by omega]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    congr 1
    omega
  rw [e]
  symm
  apply Finset.sum_subset
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    simp only [Finset.mem_Ico]
    omega
  · intro k hk hk'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, not_and, not_lt] at hk hk'
    apply hr
    by_contra h
    exact absurd (hk' (by omega)) (by omega)

/- English proof (translation)
Introduce `n a j r hj ha hz`. Establish `hpairs : ∑ c ∈ range (2 * a + 1), ∑ b ∈ range (2 * a + 1), r b * r (b + c + 1) = ∑ b ∈ range (2 * a + 1), ∑ k ∈ (range (2 * a + 1)).filter (fun k => b < k), r b * r k`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl (fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[← Finset.mul_sum, ← Finset.mul_sum, sum_shift_eq (2 * a + 1) r hz b]`.

Establish `hsum : ∑ b ∈ range (2 * a + 1), r b = 2 * ∑ i, j i + (n - 2 * ∑ i, j i)`. Establish `h : ∑ b ∈ range (2 * a + 1), r b = ∑ i : Fin a, (r i + r (2 * a - i)) + r a` using `GlobalTheory.DoubledFlag.sum_range_double a r`. Rewrite using `[h, ha]`. Use `congr 1`. Rewrite using `[Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[(hj i).1, (hj i).2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsq : ∑ b ∈ range (2 * a + 1), r b ^ 2 = 2 * ∑ i, j i ^ 2 + (n - 2 * ∑ i, j i) ^ 2`. Establish `h : ∑ b ∈ range (2 * a + 1), r b ^ 2 = ∑ i : Fin a, (r i ^ 2 + r (2 * a - i) ^ 2) + r a ^ 2` using `GlobalTheory.DoubledFlag.sum_range_double a (fun b => r b ^ 2)`.

Rewrite using `[h, ha]`. Use `congr 1`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[(hj i).1, (hj i).2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `two_mul_pairs_add_sq (range (2 * a + 1)) r`. Establish `h2` using `two_mul_pairs_add_sq (univ : Finset (Fin a)) j`. Rewrite `h1` using `[hsum, hsq]`. Rewrite using `[hpairs, GlobalTheory.FlagMeas.dimN]`.

Use polynomial arithmetic with `[h1, h2]`.
-/
theorem dimN_eq_sum_pairs : ∀ (n a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ), (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i → (∀ b, 2 * a + 1 ≤ b → r b = 0) → dimN n j = ∑ c ∈ Finset.range (2 * a + 1), ∑ b ∈ Finset.range (2 * a + 1), r b * r (b + c + 1) := by
  intro n a j r hj ha hz
  have hpairs : ∑ c ∈ range (2 * a + 1), ∑ b ∈ range (2 * a + 1), r b * r (b + c + 1)
      = ∑ b ∈ range (2 * a + 1), ∑ k ∈ (range (2 * a + 1)).filter (fun k => b < k), r b * r k := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_shift_eq (2 * a + 1) r hz b]
  have hsum : ∑ b ∈ range (2 * a + 1), r b = 2 * ∑ i, j i + (n - 2 * ∑ i, j i) := by
    have h : ∑ b ∈ range (2 * a + 1), r b = ∑ i : Fin a, (r i + r (2 * a - i)) + r a :=
      GlobalTheory.DoubledFlag.sum_range_double a r
    rw [h, ha]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(hj i).1, (hj i).2]
    ring
  have hsq : ∑ b ∈ range (2 * a + 1), r b ^ 2 = 2 * ∑ i, j i ^ 2 + (n - 2 * ∑ i, j i) ^ 2 := by
    have h : ∑ b ∈ range (2 * a + 1), r b ^ 2 = ∑ i : Fin a, (r i ^ 2 + r (2 * a - i) ^ 2) + r a ^ 2 :=
      GlobalTheory.DoubledFlag.sum_range_double a (fun b => r b ^ 2)
    rw [h, ha]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(hj i).1, (hj i).2]
    ring
  have h1 := two_mul_pairs_add_sq (range (2 * a + 1)) r
  have h2 := two_mul_pairs_add_sq (univ : Finset (Fin a)) j
  rw [hsum, hsq] at h1
  rw [hpairs, GlobalTheory.FlagMeas.dimN]
  nlinarith [h1, h2]

end GlobalTheory.RadicalDimSum
