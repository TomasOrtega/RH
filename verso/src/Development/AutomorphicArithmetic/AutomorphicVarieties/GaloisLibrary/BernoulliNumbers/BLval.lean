import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Hurzero
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.Sumicc

open Finset UpperTheory.V.Bern

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Establish `e : (1 : ℂ) - ((0 + 1 : ℕ) : ℂ) = 0` using `by push_cast; ring`. Rewrite using `[e, b_hurzero x h0 h1]`. Simplify using `[Polynomial.bernoulli_one]`.

Use `HurwitzZeta.hurwitzZeta_neg_nat (k := m) (x := x) hm.ne' ⟨h0.le, h1⟩` as an intermediate fact. Establish `e : (1 : ℂ) - ((m + 1 : ℕ) : ℂ) = -(m : ℂ)` using `by push_cast; ring`. Rewrite using `[e, this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem hurwitzZeta_one_sub_eq_bernoulli (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (h0 : 0 < x) (h1 : x ≤ 1) :
    HurwitzZeta.hurwitzZeta (x : UnitAddCircle) (1 - k) =
      -1 / k * ((Polynomial.bernoulli k).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have e : (1 : ℂ) - ((0 + 1 : ℕ) : ℂ) = 0 := by push_cast; ring
    rw [e, b_hurzero x h0 h1]
    simp [Polynomial.bernoulli_one]
  · have := HurwitzZeta.hurwitzZeta_neg_nat (k := m) (x := x) hm.ne' ⟨h0.le, h1⟩
    have e : (1 : ℂ) - ((m + 1 : ℕ) : ℂ) = -(m : ℂ) := by push_cast; ring
    rw [e, this]
    push_cast
    ring

/- English proof (translation)
Introduce `N _ Φ k hk`. Establish `hN : (0:ℝ) < N` using `Nat.cast_pos.mpr (NeZero.pos N)`. Establish `hpow : (N : ℂ) ^ (-(1 - (k:ℂ))) = (N:ℂ) ^ ((k:ℤ) - 1)`. Rewrite using `[show -(1 - (k:ℂ)) = (((k:ℤ) - 1 : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]`. Rewrite using `[ZMod.LFunction, hpow, ← b_sumicc, genB, Finset.mul_sum, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]`.

Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `a ha`. Rewrite `ha` using `[Finset.mem_Icc]`. Establish `hx0 : (0:ℝ) < a / N` using `div_pos (by exact_mod_cast ha.1) hN`. Establish `hx1 : (a:ℝ) / N ≤ 1` using `(div_le_one hN).mpr (by exact_mod_cast ha.2)`.

Rewrite using `[ZMod.toAddCircle_natCast, hurwitzZeta_one_sub_eq_bernoulli k hk _ hx0 hx1, bcoef, map_mul, map_zpow₀, map_natCast, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]`. Establish `hk0 : (k:ℂ) ≠ 0` using `by exact_mod_cast (by omega : k ≠ 0)`. Establish `hq : (algebraMap ℚ ℂ) ((a:ℚ) / N) = (((a:ℝ) / N : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[hq]`. Clear the denominators using the available nonvanishing facts.
-/
theorem UpperTheory.V.Bern.b_lval :
    ∀ {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (k : ℕ), 1 ≤ k → ZMod.LFunction Φ (1 - k) = -genB k Φ / k := by
  intro N _ Φ k hk
  have hN : (0:ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hpow : (N : ℂ) ^ (-(1 - (k:ℂ))) = (N:ℂ) ^ ((k:ℤ) - 1) := by
    rw [show -(1 - (k:ℂ)) = (((k:ℤ) - 1 : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  rw [ZMod.LFunction, hpow, ← b_sumicc, genB, Finset.mul_sum, neg_div, Finset.sum_div,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_Icc] at ha
  have hx0 : (0:ℝ) < a / N := div_pos (by exact_mod_cast ha.1) hN
  have hx1 : (a:ℝ) / N ≤ 1 := (div_le_one hN).mpr (by exact_mod_cast ha.2)
  rw [ZMod.toAddCircle_natCast, hurwitzZeta_one_sub_eq_bernoulli k hk _ hx0 hx1, bcoef, map_mul, map_zpow₀,
    map_natCast, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map]
  have hk0 : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hq : (algebraMap ℚ ℂ) ((a:ℚ) / N) = (((a:ℝ) / N : ℝ) : ℂ) := by push_cast; rfl
  rw [hq]
  field_simp
