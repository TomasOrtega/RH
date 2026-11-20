import Formalism.SharpRestriction.GrowthBounds.RootWeights.RestAOfHighestVectorIntegrality

noncomputable section

open Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Rewrite using `[Finset.sum_range_succ' (fun j => c' j • B j), h0]`. Establish `e1 : ∑ j ∈ range (k + 1), c' (j + 1) • B (j + 1) = ∑ j ∈ range (k + 1), (c (j + 1) • B (j + 1) + (c j * r j) • B (j + 1))`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j hj`. Rewrite using `[hs j (Finset.mem_range.mp hj), add_smul]`.

Rewrite using `[e1, Finset.sum_add_distrib]`. Establish `e2 : ∑ j ∈ range (k + 1), c j • (B j + r j • B (j + 1)) = ∑ j ∈ range (k + 1), c j • B j + ∑ j ∈ range (k + 1), (c j * r j) • B (j + 1)`. Rewrite using `[← Finset.sum_add_distrib]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j _`.

Rewrite using `[smul_add, smul_smul]`. Rewrite using `[e2]`. Establish `e3 : ∑ j ∈ range (k + 1), c j • B j = c 0 • B 0 + ∑ j ∈ range (k + 1), c (j + 1) • B (j + 1)`. Rewrite using `[Finset.sum_range_succ (fun j => c (j + 1) • B (j + 1)), hz, zero_smul, add_zero, Finset.sum_range_succ' (fun j => c j • B j)]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e3]`. Normalize the expressions using the abelian group laws.
-/
theorem weighted_sum_shift_recombine {K M : Type*} [Field K] [AddCommGroup M] [Module K M] (c c' r : ℕ → K) (B : ℕ → M) (k : ℕ)
    (h0 : c' 0 = c 0) (hs : ∀ j, j < k + 1 → c' (j + 1) = c (j + 1) + c j * r j) (hz : c (k + 1) = 0) :
    ∑ j ∈ range (k + 1), c j • (B j + r j • B (j + 1)) = ∑ j ∈ range (k + 2), c' j • B j := by
  rw [Finset.sum_range_succ' (fun j => c' j • B j), h0]
  have e1 : ∑ j ∈ range (k + 1), c' (j + 1) • B (j + 1) =
      ∑ j ∈ range (k + 1), (c (j + 1) • B (j + 1) + (c j * r j) • B (j + 1)) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hs j (Finset.mem_range.mp hj), add_smul]
  rw [e1, Finset.sum_add_distrib]
  have e2 : ∑ j ∈ range (k + 1), c j • (B j + r j • B (j + 1)) =
      ∑ j ∈ range (k + 1), c j • B j + ∑ j ∈ range (k + 1), (c j * r j) • B (j + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_add, smul_smul]
  rw [e2]
  have e3 : ∑ j ∈ range (k + 1), c j • B j =
      c 0 • B 0 + ∑ j ∈ range (k + 1), c (j + 1) • B (j + 1) := by
    rw [Finset.sum_range_succ (fun j => c (j + 1) • B (j + 1)), hz, zero_smul, add_zero,
      Finset.sum_range_succ' (fun j => c j • B j)]
    abel
  rw [e3]
  abel

section Heisenberg₂

variable {K A : Type*} [Field K] [CharZero K] [Ring A] [Algebra K A]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Establish `e1 : X * Y ^ (m + 1) = (X * Y ^ m) * Y` using `by rw [pow_succ, mul_assoc]`. Establish `e2 : Y ^ (m - 1) * Z * Y = Y ^ (m - 1) * Y * Z` using `by rw [mul_assoc, hZY, ← mul_assoc]`.

Rewrite using `[e1, ih, add_mul, mul_assoc (Y ^ m) X Y, hZ, smul_mul_assoc, e2, mul_add, ← mul_assoc, ← pow_succ]`. Break down `Nat.eq_zero_or_pos m with rfl | hm` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[← pow_succ, Nat.sub_add_cancel hm]`. Simplify using `only [Nat.add_sub_cancel, Nat.cast_succ, add_smul, one_smul]`.

Normalize the expressions using the abelian group laws.
-/
theorem heisenberg_mul_pow_commutator {X Y Z : A} (hZ : X * Y = Y * X + Z) (hZY : Z * Y = Y * Z) (m : ℕ) :
    X * Y ^ m = Y ^ m * X + (m : K) • (Y ^ (m - 1) * Z) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e1 : X * Y ^ (m + 1) = (X * Y ^ m) * Y := by rw [pow_succ, mul_assoc]
    have e2 : Y ^ (m - 1) * Z * Y = Y ^ (m - 1) * Y * Z := by rw [mul_assoc, hZY, ← mul_assoc]
    rw [e1, ih, add_mul, mul_assoc (Y ^ m) X Y, hZ, smul_mul_assoc, e2, mul_add, ← mul_assoc, ← pow_succ]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [← pow_succ, Nat.sub_add_cancel hm]
      simp only [Nat.add_sub_cancel, Nat.cast_succ, add_smul, one_smul]
      abel

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `hc : ∀ j : ℕ, Commute X (Z ^ j)` using `fun j => Commute.pow_right (show Commute X Z from hZX) j`. Establish `step : ∀ j ∈ range (k + 1), X * ((((k.choose j * l.descFactorial j : ℕ)) : K) • (Y ^ (l - j) * Z ^ j * X ^ (k - j))) = (((k.choose j * l.descFactorial j : ℕ)) : K) • (Y ^ (l - j) * Z ^ j * X ^ (k + 1 - j) + (((l - j : ℕ)) : K) • (Y ^ (l - (j + 1)) * Z ^ (j + 1) * X ^ (k + 1 - (j …`.

Introduce `j hj`. Establish `hjk : j ≤ k` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)`. Rewrite using `[mul_smul_comm]`. Use `congr 1`. Rewrite using `[← mul_assoc, ← mul_assoc, heisenberg_mul_pow_commutator (K := K) hZ hZY (l - j), add_mul, add_mul, smul_mul_assoc, smul_mul_assoc]`.

Use `congr 1`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc X (Z ^ j), (hc j).eq, mul_assoc (Z ^ j), ← pow_succ', show k - j + 1 = k + 1 - j by omega]`. Use `congr 1`. Rewrite using `[show l - (j + 1) = l - j - 1 by omega, show k + 1 - (j + 1) = k - j by omega, mul_assoc (Y ^ (l - j - 1)) Z, ← pow_succ']`.

Rewrite using `[pow_succ', mul_assoc, ih, Finset.mul_sum, Finset.sum_congr rfl step]`. Conclude with `weighted_sum_shift_recombine (fun j => ((k.choose j * l.descFactorial j : ℕ) : K)) (fun j => (((k + 1).choose j * l.descFactorial j : ℕ) : K)) (fun j => ((l - j : ℕ) : K)) (fun j => Y ^ (l - j) * Z ^ j * X ^ (k + 1 - j)) k (by simp) (fun j _ => by`. Establish `e : (k + 1).choose (j + 1) * l.descFactorial (j + 1) = k.choose (j + 1) * l.descFactorial (j + 1) + k.choose j * l.descFactorial j * (l - j)`. Rewrite using `[Nat.choose_succ_succ, Nat.descFactorial_succ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `push_cast`. Use the proof step `ring)`. Use the proof step `(by simp [Nat.choose_succ_self])`.
-/
theorem heisenberg_pow_mul_pow_expansion {X Y Z : A} (hZ : X * Y = Y * X + Z) (hZY : Z * Y = Y * Z) (hZX : X * Z = Z * X) (k l : ℕ) :
    X ^ k * Y ^ l = ∑ j ∈ range (k + 1),
      (((k.choose j * l.descFactorial j : ℕ) : K)) • (Y ^ (l - j) * Z ^ j * X ^ (k - j)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : ∀ j : ℕ, Commute X (Z ^ j) := fun j => Commute.pow_right (show Commute X Z from hZX) j
    have step : ∀ j ∈ range (k + 1),
        X * ((((k.choose j * l.descFactorial j : ℕ)) : K) • (Y ^ (l - j) * Z ^ j * X ^ (k - j))) =
        (((k.choose j * l.descFactorial j : ℕ)) : K) • (Y ^ (l - j) * Z ^ j * X ^ (k + 1 - j) +
          (((l - j : ℕ)) : K) • (Y ^ (l - (j + 1)) * Z ^ (j + 1) * X ^ (k + 1 - (j + 1)))) := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [mul_smul_comm]
      congr 1
      rw [← mul_assoc, ← mul_assoc, heisenberg_mul_pow_commutator (K := K) hZ hZY (l - j), add_mul, add_mul,
        smul_mul_assoc, smul_mul_assoc]
      congr 1
      · simp only [mul_assoc]
        rw [← mul_assoc X (Z ^ j), (hc j).eq, mul_assoc (Z ^ j), ← pow_succ',
          show k - j + 1 = k + 1 - j by omega]
      · congr 1
        rw [show l - (j + 1) = l - j - 1 by omega, show k + 1 - (j + 1) = k - j by omega,
          mul_assoc (Y ^ (l - j - 1)) Z, ← pow_succ']
    rw [pow_succ', mul_assoc, ih, Finset.mul_sum, Finset.sum_congr rfl step]
    exact weighted_sum_shift_recombine (fun j => ((k.choose j * l.descFactorial j : ℕ) : K))
      (fun j => (((k + 1).choose j * l.descFactorial j : ℕ) : K)) (fun j => ((l - j : ℕ) : K))
      (fun j => Y ^ (l - j) * Z ^ j * X ^ (k + 1 - j)) k (by simp)
      (fun j _ => by
        have e : (k + 1).choose (j + 1) * l.descFactorial (j + 1) =
            k.choose (j + 1) * l.descFactorial (j + 1) + k.choose j * l.descFactorial j * (l - j) := by
          rw [Nat.choose_succ_succ, Nat.descFactorial_succ]; ring
        rw [e]
        push_cast
        ring)
      (by simp [Nat.choose_succ_self])

def dividedPower (K : Type*) [Field K] {A : Type*} [Ring A] [Algebra K A] (X : A) (k : ℕ) : A := ((k.factorial : K)⁻¹) • X ^ k

/- English proof (translation)
Unfold `dividedPower`. Rewrite using `[smul_mul_smul_comm, heisenberg_pow_mul_pow_expansion (K := K) hZ hZY hZX, Finset.smul_sum]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `j hj`. Establish `hjk : j ≤ k` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)`.

Use `split_ifs with hjl`. Rewrite using `[smul_smul, smul_mul_smul_comm, smul_mul_smul_comm]`. Use `congr 1`. Establish `h1 : ((k.factorial : ℕ) : K) = (k.choose j : K) * j.factorial * (k - j).factorial`. Conclude with `(Nat.choose_mul_factorial_mul_factorial hjk).symm` after adjusting the coercions.

Establish `h2 : ((l.factorial : ℕ) : K) = ((l - j).factorial : K) * l.descFactorial j`. Conclude with `(Nat.factorial_mul_descFactorial hjl).symm` after adjusting the coercions. Establish `h3 : (k.choose j : K) ≠ 0` using `by exact_mod_cast (Nat.choose_pos hjk).ne'`. Establish `h4 : (l.descFactorial j : K) ≠ 0`. Conclude with `(Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))` after adjusting the coercions.

Establish `h5 : (j.factorial : K) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero _`. Establish `h6 : ((k - j).factorial : K) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero _`. Establish `h7 : ((l - j).factorial : K) ≠ 0` using `by exact_mod_cast Nat.factorial_ne_zero _`. Rewrite using `[h1, h2]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Establish `h0 : l.descFactorial j = 0` using `Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)`. Simplify using `[h0]`.
-/
theorem heisenberg_dividedPower_expansion {X Y Z : A} (hZ : X * Y = Y * X + Z) (hZY : Z * Y = Y * Z) (hZX : X * Z = Z * X) (k l : ℕ) :
    dividedPower K X k * dividedPower K Y l = ∑ j ∈ range (k + 1),
      if j ≤ l then dividedPower K Y (l - j) * dividedPower K Z j * dividedPower K X (k - j) else 0 := by
  unfold dividedPower
  rw [smul_mul_smul_comm, heisenberg_pow_mul_pow_expansion (K := K) hZ hZY hZX, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  split_ifs with hjl
  · rw [smul_smul, smul_mul_smul_comm, smul_mul_smul_comm]
    congr 1
    have h1 : ((k.factorial : ℕ) : K) = (k.choose j : K) * j.factorial * (k - j).factorial := by
      exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hjk).symm
    have h2 : ((l.factorial : ℕ) : K) = ((l - j).factorial : K) * l.descFactorial j := by
      exact_mod_cast (Nat.factorial_mul_descFactorial hjl).symm
    have h3 : (k.choose j : K) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjk).ne'
    have h4 : (l.descFactorial j : K) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
    have h5 : (j.factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h6 : ((k - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h7 : ((l - j).factorial : K) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    rw [h1, h2]
    push_cast
    field_simp
  · have h0 : l.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    simp [h0]

end Heisenberg₂

end Formalism.MainNotions.G.GLWeightTheory
