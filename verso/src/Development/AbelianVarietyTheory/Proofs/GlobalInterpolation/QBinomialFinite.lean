import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple.QBinomial

open GlobalTheory.JacobiTriple

/- English proof (translation)
Unfold `qPoch`. Rewrite using `[Finset.prod_range_succ]`.
-/
theorem qPoch_succ (t : ℂ) (n : ℕ) : qPoch t (n + 1) = qPoch t n * (1 - t ^ (n + 1)) := by
  unfold qPoch; rw [Finset.prod_range_succ]

/- English proof (translation)
Establish `h` using `(qPoch_tendsto t ht).2.2 m`. Unfold `qBinom; rw [show qPoch t 0 = 1 by simp [qPoch], Nat.sub_zero]; field_simp`.
-/
theorem qBinom_zero_right (t : ℂ) (ht : ‖t‖ < 1) (m : ℕ) : qBinom t m 0 = 1 := by
  have h := (qPoch_tendsto t ht).2.2 m
  unfold qBinom; rw [show qPoch t 0 = 1 by simp [qPoch], Nat.sub_zero]; field_simp

/- English proof (translation)
Establish `h` using `(qPoch_tendsto t ht).2.2 m`. Unfold `qBinom; simp [Nat.sub_self]; rw [show qPoch t 0 = 1 by simp [qPoch]]; field_simp`.
-/
theorem qBinom_self (t : ℂ) (ht : ‖t‖ < 1) (m : ℕ) : qBinom t m m = 1 := by
  have h := (qPoch_tendsto t ht).2.2 m
  unfold qBinom; simp [Nat.sub_self]; rw [show qPoch t 0 = 1 by simp [qPoch]]; field_simp

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ j, m = k + 1 + j` from `⟨m - (k + 1), by omega⟩`. Establish `hne` using `(qPoch_tendsto t ht).2.2`. Establish `e1 : k + 1 + j + 1 - (k + 1) = j + 1` using `by omega`. Establish `e2 : k + 1 + j - (k + 1) = j` using `by omega`. Establish `e3 : k + 1 + j - k = j + 1` using `by omega`.

Unfold `qBinom`. Rewrite using `[e1, e2, e3, qPoch_succ t (k + 1 + j), qPoch_succ t k, qPoch_succ t j]`. Establish `hk1 : (1 - t ^ (k + 1)) ≠ 0`. Use `hne (k + 1)` as an intermediate fact. Rewrite `this` using `[qPoch_succ]`.

Conclude with `right_ne_zero_of_mul this`. Establish `hj1 : (1 - t ^ (j + 1)) ≠ 0`. Use `hne (j + 1)` as an intermediate fact. Rewrite `this` using `[qPoch_succ]`. Conclude with `right_ne_zero_of_mul this`.

Establish `hk0` using `hne k`. Establish `hj0` using `hne j`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qBinom_pascal (t : ℂ) (ht : ‖t‖ < 1) (m k : ℕ) (hk : k < m) :
    qBinom t (m + 1) (k + 1) = qBinom t m (k + 1) + t ^ (m - k) * qBinom t m k := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - (k + 1), by omega⟩
  have hne := (qPoch_tendsto t ht).2.2
  have e1 : k + 1 + j + 1 - (k + 1) = j + 1 := by omega
  have e2 : k + 1 + j - (k + 1) = j := by omega
  have e3 : k + 1 + j - k = j + 1 := by omega
  unfold qBinom
  rw [e1, e2, e3, qPoch_succ t (k + 1 + j), qPoch_succ t k, qPoch_succ t j]
  have hk1 : (1 - t ^ (k + 1)) ≠ 0 := by
    have := hne (k + 1); rw [qPoch_succ] at this; exact right_ne_zero_of_mul this
  have hj1 : (1 - t ^ (j + 1)) ≠ 0 := by
    have := hne (j + 1); rw [qPoch_succ] at this; exact right_ne_zero_of_mul this
  have hk0 := hne k
  have hj0 := hne j
  field_simp
  ring

/- English proof (translation)
Take `⟨j, rfl⟩ : ∃ j, m = k + 1 + j` from `⟨m - (k + 1), by omega⟩`. Rewrite using `[show k + 1 + j - k = j + 1 by omega]`. Break down `k with _ | k` into its components or cases. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Nat.add_sub_cancel]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_eq (m k : ℕ) (hk : k < m) : k * (k - 1) + 2 * m = (k + 1) * k + 2 * (m - k) := by
  obtain ⟨j, rfl⟩ : ∃ j, m = k + 1 + j := ⟨m - (k + 1), by omega⟩
  rw [show k + 1 + j - k = j + 1 by omega]
  rcases k with _ | k
  · ring
  · simp only [Nat.add_sub_cancel]; ring

/- English proof (translation)
Introduce `s X hs m`. Establish `ht : ‖s ^ 2‖ < 1`. Rewrite using `[norm_pow]`. Use polynomial arithmetic with `[norm_nonneg s]`. Proceed by induction on `m with`.

Consider the case `zero => simp [qBinom_zero_right _ ht]`. Consider the case `succ m ih => set f : ℕ → ℕ → ℂ := fun m k => qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k with hf`. Express the relevant statement in the definitionally equal form `∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), f m k at ih`. Express the relevant statement in the definitionally equal form `_ = ∑ k ∈ Finset.range (m + 1 + 1), f (m + 1) k`. Rewrite using `[Finset.prod_range_succ, ih, mul_add, mul_one]`.

Establish `A : ∑ k ∈ Finset.range (m + 1), f m k = f m 0 + ∑ k ∈ Finset.range m, f m (k + 1)`. Rewrite using `[Finset.sum_range_succ', add_comm]`. Establish `B : (∑ k ∈ Finset.range (m + 1), f m k) * (X * s ^ (2 * m)) = ∑ k ∈ Finset.range m, f m k * (X * s ^ (2 * m)) + f m m * (X * s ^ (2 * m))`. Rewrite using `[Finset.sum_mul, Finset.sum_range_succ]`. Establish `C : ∑ k ∈ Finset.range (m + 1 + 1), f (m + 1) k = f (m + 1) 0 + ∑ k ∈ Finset.range m, f (m + 1) (k + 1) + f (m + 1) (m + 1)`.

Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ', add_comm (f (m + 1) 0)]`. Establish `hsum : ∑ k ∈ Finset.range m, f (m + 1) (k + 1) = ∑ k ∈ Finset.range m, f m (k + 1) + ∑ k ∈ Finset.range m, f m k * (X * s ^ (2 * m))`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl (fun k hk => ?_)` and prove the remaining obligations. Establish `hk'` using `Finset.mem_range.mp hk`.

Simplify using `only [hf]`. Rewrite using `[qBinom_pascal _ ht m k hk']`. Establish `: s ^ (k * (k - 1)) * s ^ (2 * m) = s ^ ((k + 1) * k) * (s ^ 2) ^ (m - k)`. Rewrite using `[← pow_add, ← pow_mul, ← pow_add, exp_eq m k hk']`. Simplify using `only [Nat.add_sub_cancel]`.

Take the linear combination `(-(qBinom (s ^ 2) m k * X ^ (k + 1))) * this`. Establish `hlast : s ^ ((m + 1) * (m + 1 - 1)) = s ^ (m * (m - 1)) * s ^ (2 * m)`. Rewrite using `[← pow_add]`. Use `congr 1`. Break down `m with _ | m` into its components or cases.

Simplify using the standard rewrite rules. Simplify using `only [Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Establish `e0 : f (m + 1) 0 = f m 0`. Simplify using `only [hf, qBinom_zero_right _ ht]`.

Establish `em : f (m + 1) (m + 1) = f m m * (X * s ^ (2 * m))`. Simplify using `only [hf, qBinom_self _ ht, hlast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[B, A, C, hsum, e0, em]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem qBinomial_finite : ∀ (s X : ℂ), ‖s‖ < 1 → ∀ m : ℕ, ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), GlobalTheory.JacobiTriple.qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k := by
  intro s X hs m
  have ht : ‖s ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg s]
  induction m with
  | zero => simp [qBinom_zero_right _ ht]
  | succ m ih =>
    set f : ℕ → ℕ → ℂ := fun m k => qBinom (s ^ 2) m k * s ^ (k * (k - 1)) * X ^ k with hf
    change ∏ k ∈ Finset.range m, (1 + X * s ^ (2 * k)) = ∑ k ∈ Finset.range (m + 1), f m k at ih
    change _ = ∑ k ∈ Finset.range (m + 1 + 1), f (m + 1) k
    rw [Finset.prod_range_succ, ih, mul_add, mul_one]
    have A : ∑ k ∈ Finset.range (m + 1), f m k = f m 0 + ∑ k ∈ Finset.range m, f m (k + 1) := by
      rw [Finset.sum_range_succ', add_comm]
    have B : (∑ k ∈ Finset.range (m + 1), f m k) * (X * s ^ (2 * m)) =
        ∑ k ∈ Finset.range m, f m k * (X * s ^ (2 * m)) + f m m * (X * s ^ (2 * m)) := by
      rw [Finset.sum_mul, Finset.sum_range_succ]
    have C : ∑ k ∈ Finset.range (m + 1 + 1), f (m + 1) k =
        f (m + 1) 0 + ∑ k ∈ Finset.range m, f (m + 1) (k + 1) + f (m + 1) (m + 1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ', add_comm (f (m + 1) 0)]
    have hsum : ∑ k ∈ Finset.range m, f (m + 1) (k + 1)
        = ∑ k ∈ Finset.range m, f m (k + 1) + ∑ k ∈ Finset.range m, f m k * (X * s ^ (2 * m)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' := Finset.mem_range.mp hk
      simp only [hf]
      rw [qBinom_pascal _ ht m k hk']
      have : s ^ (k * (k - 1)) * s ^ (2 * m) = s ^ ((k + 1) * k) * (s ^ 2) ^ (m - k) := by
        rw [← pow_add, ← pow_mul, ← pow_add, exp_eq m k hk']
      simp only [Nat.add_sub_cancel]
      linear_combination (-(qBinom (s ^ 2) m k * X ^ (k + 1))) * this
    have hlast : s ^ ((m + 1) * (m + 1 - 1)) = s ^ (m * (m - 1)) * s ^ (2 * m) := by
      rw [← pow_add]; congr 1; rcases m with _ | m
      · simp
      · simp only [Nat.add_sub_cancel]; ring
    have e0 : f (m + 1) 0 = f m 0 := by
      simp only [hf, qBinom_zero_right _ ht]
    have em : f (m + 1) (m + 1) = f m m * (X * s ^ (2 * m)) := by
      simp only [hf, qBinom_self _ ht, hlast]; ring
    rw [B, A, C, hsum, e0, em]
    ring

end GlobalTheory.JacobiTriple.QBinomial
