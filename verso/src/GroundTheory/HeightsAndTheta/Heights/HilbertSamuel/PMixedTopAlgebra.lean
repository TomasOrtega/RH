import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedTopAlgebra
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolyNonnegAtZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Filter Polynomial

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Establish `hid : i ≤ d` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`. Establish `hpow : Q ^ d = Q ^ (d - i) * Q ^ i` using `by rw [← pow_add, Nat.sub_add_cancel hid]`. Rewrite using `[hpow, div_pow]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem MixedTopAlgebra.clear_den (d : ℕ) (m : ℕ → ℝ) (Q x : ℝ) (hQ : Q ≠ 0) :
    Q ^ d * ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * m i * (x / Q) ^ i =
      ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hpow : Q ^ d = Q ^ (d - i) * Q ^ i := by rw [← pow_add, Nat.sub_add_cancel hid]
  rw [hpow, div_pow]
  field_simp

/- English proof (translation)
Rewrite using `[Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, Finset.mul_sum]`. Simplify using `only [Nat.cast_one, one_mul, mul_one]`. Use `add_le_add (Finset.sum_le_sum fun i hi => ?_) le_rfl` and prove the remaining obligations. Establish `hid : i < d` using `Finset.mem_range.mp hi`. Establish `hpow : Q * Q ^ (d - 1 - i) = Q ^ (d - i)`.

Rewrite using `[← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Break down `Nat.eq_zero_or_pos i with rfl | hi0` into its components or cases.

Simplify using the standard rewrite rules. Establish `hmi : 0 ≤ m i` using `hm i hi0 hid.le`. Establish `hc : ((d - 1).choose i : ℝ) ≤ (d.choose i : ℝ)`. Conclude with `Nat.choose_le_choose i (Nat.sub_le d 1)` after adjusting the coercions. Use `gcongr`.
-/
theorem MixedTopAlgebra.sum_ge (d : ℕ) (m : ℕ → ℝ) (hm : ∀ i, 1 ≤ i → i ≤ d → 0 ≤ m i)
    (Q x : ℝ) (hQ : 0 ≤ Q) (hx : 0 ≤ x) :
    Q * ∑ i ∈ Finset.range d, ((d - 1).choose i : ℝ) * Q ^ (d - 1 - i) * x ^ i * m i
        + x ^ d * m d ≤
      ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.sub_self, pow_zero, Finset.mul_sum]
  simp only [Nat.cast_one, one_mul, mul_one]
  refine add_le_add (Finset.sum_le_sum fun i hi => ?_) le_rfl
  have hid : i < d := Finset.mem_range.mp hi
  have hpow : Q * Q ^ (d - 1 - i) = Q ^ (d - i) := by
    rw [← pow_succ']; congr 1; omega
  calc Q * (((d - 1).choose i : ℝ) * Q ^ (d - 1 - i) * x ^ i * m i)
      = ((d - 1).choose i : ℝ) * (Q * Q ^ (d - 1 - i)) * x ^ i * m i := by ring
    _ = ((d - 1).choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by rw [hpow]
    _ ≤ (d.choose i : ℝ) * Q ^ (d - i) * x ^ i * m i := by
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · simp
      · have hmi : 0 ≤ m i := hm i hi0 hid.le
        have hc : ((d - 1).choose i : ℝ) ≤ (d.choose i : ℝ) := by
          exact_mod_cast Nat.choose_le_choose i (Nat.sub_le d 1)
        gcongr

/- English proof (translation)
Introduce `d m hd hm hmd hST`. Use `set P : Polynomial ℝ := ∑ i ∈ Finset.range (d + 1), C ((d.choose i : ℝ) * m i) * X ^ i with hPdef`. Establish `heval : ∀ t : ℝ, P.eval t = ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * m i * t ^ i`. Introduce `t`. Simplify using `[P, eval_finsetSum]`.

Establish `h0 : P.eval 0 = m 0`. Rewrite using `[heval, Finset.sum_eq_single 0]`. Simplify using the standard rewrite rules. Introduce `i _ hi`. Simplify using `[zero_pow hi]`.

Introduce `h`. Simplify using `at h`. Rewrite using `[← h0]`. Use `hP d P (m d) hmd ?_ ?_` and prove the remaining obligations. Introduce `t ht hPt`.

Take `⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = t.num` from `⟨t.num.toNat, Int.toNat_of_nonneg (Rat.num_nonneg.mpr ht.le)⟩`. Establish `hp1 : 1 ≤ p`. Establish `: 0 < t.num` using `Rat.num_pos.mpr ht`. Use linear arithmetic over natural numbers and integers. Establish `hq0 : (0 : ℝ) < (t.den : ℝ)` using `by exact_mod_cast t.den_pos`.

Establish `htq : (t : ℝ) = (p : ℝ) / (t.den : ℝ)`. Rewrite using `[Rat.cast_def, ← hp]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hS` using `MixedTopAlgebra.clear_den d m (t.den : ℝ) (p : ℝ) hq0.ne'`.

Rewrite `hS` using `[← htq, ← heval]`. Establish `hSpos : 0 < ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * (t.den : ℝ) ^ (d - i) * (p : ℝ) ^ i * m i`. Rewrite using `[← hS]`. Check the signs of the components of the expression. Establish `hT` using `hST t.den p t.den_pos hp1 hSpos`.

Establish `hge` using `MixedTopAlgebra.sum_ge d m hm (t.den : ℝ) (p : ℝ) hq0.le (by positivity)`. Establish `hqd : (0 : ℝ) < (t.den : ℝ) ^ d` using `by positivity`. Establish `hmt : (t.den : ℝ) ^ d * (m d * (t : ℝ) ^ d) = (p : ℝ) ^ d * m d`. Rewrite using `[htq, div_pow]`. Clear the denominators using the available nonvanishing facts.

Use `le_of_mul_le_mul_left ?_ hqd` and prove the remaining obligations. Rewrite using `[hmt, hS]`. Use polynomial arithmetic with `[mul_nonneg hq0.le hT]`. Establish `hlow : ∀ t : ℝ, 0 ≤ t → m 0 + m d * t ^ d ≤ P.eval t`. Introduce `t ht`.

Establish `hsub : ({0, d} : Finset ℕ) ⊆ Finset.range (d + 1)`. Introduce `i hi`. Simplify using `at hi`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers.

Rewrite using `[heval]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_pair (by omega)]; simp`. Use `_ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi hi' => by`. Establish `h1 : 1 ≤ i` using `by simp at hi'; omega`.

Use `hm i h1 (by simp at hi; omega)` as an intermediate fact. Check the signs of the components of the expression. Use `filter_upwards [eventually_ge_atTop (max 1 ((|m 0| + 1) / m d))] with t ht`. Establish `ht1 : 1 ≤ t` using `le_of_max_le_left ht`. Establish `ht2 : (|m 0| + 1) / m d ≤ t` using `le_of_max_le_right ht`.

Establish `htd : t ≤ t ^ d`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : |m 0| + 1 ≤ m d * t` using `by rw [div_le_iff₀ hmd] at ht2; linarith`. Establish `h4 : m d * t ≤ m d * t ^ d` using `mul_le_mul_of_nonneg_left htd hmd.le`. Establish `h5` using `hlow t (by linarith)`.

Combine the linear relations using `[neg_abs_le (m 0)]`.
-/
theorem MixedTopAlgebra.proof (hP : PolyNonnegAtZero.Statement) : MixedTopAlgebra.Statement := by
  intro d m hd hm hmd hST
  set P : Polynomial ℝ := ∑ i ∈ Finset.range (d + 1), C ((d.choose i : ℝ) * m i) * X ^ i with hPdef
  have heval : ∀ t : ℝ, P.eval t = ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * m i * t ^ i := by
    intro t; simp [P, eval_finsetSum]
  have h0 : P.eval 0 = m 0 := by
    rw [heval, Finset.sum_eq_single 0]
    · simp
    · intro i _ hi; simp [zero_pow hi]
    · intro h; simp at h
  rw [← h0]
  refine hP d P (m d) hmd ?_ ?_
  · intro t ht hPt
    obtain ⟨p, hp⟩ : ∃ p : ℕ, (p : ℤ) = t.num :=
      ⟨t.num.toNat, Int.toNat_of_nonneg (Rat.num_nonneg.mpr ht.le)⟩
    have hp1 : 1 ≤ p := by
      have : 0 < t.num := Rat.num_pos.mpr ht
      omega
    have hq0 : (0 : ℝ) < (t.den : ℝ) := by exact_mod_cast t.den_pos
    have htq : (t : ℝ) = (p : ℝ) / (t.den : ℝ) := by
      rw [Rat.cast_def, ← hp]; push_cast; rfl
    have hS := MixedTopAlgebra.clear_den d m (t.den : ℝ) (p : ℝ) hq0.ne'
    rw [← htq, ← heval] at hS
    have hSpos : 0 < ∑ i ∈ Finset.range (d + 1),
        (d.choose i : ℝ) * (t.den : ℝ) ^ (d - i) * (p : ℝ) ^ i * m i := by
      rw [← hS]; positivity
    have hT := hST t.den p t.den_pos hp1 hSpos
    have hge := MixedTopAlgebra.sum_ge d m hm (t.den : ℝ) (p : ℝ) hq0.le (by positivity)
    have hqd : (0 : ℝ) < (t.den : ℝ) ^ d := by positivity
    have hmt : (t.den : ℝ) ^ d * (m d * (t : ℝ) ^ d) = (p : ℝ) ^ d * m d := by
      rw [htq, div_pow]; field_simp
    refine le_of_mul_le_mul_left ?_ hqd
    rw [hmt, hS]
    nlinarith [mul_nonneg hq0.le hT]
  · have hlow : ∀ t : ℝ, 0 ≤ t → m 0 + m d * t ^ d ≤ P.eval t := by
      intro t ht
      have hsub : ({0, d} : Finset ℕ) ⊆ Finset.range (d + 1) := by
        intro i hi; simp at hi; simp; omega
      rw [heval]
      calc m 0 + m d * t ^ d = ∑ i ∈ ({0, d} : Finset ℕ), (d.choose i : ℝ) * m i * t ^ i := by
            rw [Finset.sum_pair (by omega)]; simp
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi hi' => by
            have h1 : 1 ≤ i := by simp at hi'; omega
            have := hm i h1 (by simp at hi; omega)
            positivity
    filter_upwards [eventually_ge_atTop (max 1 ((|m 0| + 1) / m d))] with t ht
    have ht1 : 1 ≤ t := le_of_max_le_left ht
    have ht2 : (|m 0| + 1) / m d ≤ t := le_of_max_le_right ht
    have htd : t ≤ t ^ d := by
      calc t = t ^ 1 := (pow_one t).symm
        _ ≤ t ^ d := pow_le_pow_right₀ ht1 (by omega)
    have h3 : |m 0| + 1 ≤ m d * t := by rw [div_le_iff₀ hmd] at ht2; linarith
    have h4 : m d * t ≤ m d * t ^ d := mul_le_mul_of_nonneg_left htd hmd.le
    have h5 := hlow t (by linarith)
    linarith [neg_abs_le (m 0)]

end GroundTheory.Heights₂.Heights.HilbertSamuel
