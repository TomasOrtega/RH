import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

namespace NearUnitaryExp

open scoped Matrix.Norms.Frobenius

/- English proof (translation)
Establish `hx` using `(hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x)`. Establish `hr` using `(hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)`. Rewrite `hr` using `[← Real.exp_eq_exp_ℝ]`. Simplify using `only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul] at hx hr`. Use `hx.norm_le_of_bounded hr fun m => ?_` and prove the remaining obligations.

Rewrite using `[norm_smul, smul_eq_mul, norm_inv, Complex.norm_natCast]`. Conclude with `mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos m)) (by positivity)`.
-/
theorem norm_exp_sub_one_le_exp_norm {A : Type*} [NormedRing A] [NormedAlgebra ℂ A]
    [CompleteSpace A] (x : A) : ‖NormedSpace.exp x - 1‖ ≤ Real.exp ‖x‖ - 1 := by
  have hx := (hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) x)
  have hr := (hasSum_nat_add_iff' 1).mpr (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ‖x‖)
  rw [← Real.exp_eq_exp_ℝ] at hr
  simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, inv_one,
    pow_zero, one_smul] at hx hr
  refine hx.norm_le_of_bounded hr fun m => ?_
  rw [norm_smul, smul_eq_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' x (Nat.succ_pos m)) (by positivity)

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[frobenius_norm_def, Real.sqrt_eq_rpow, hs]`. Simplify using `only [Real.rpow_two]`.
-/
theorem sqrt_hs_eq_norm (A : Matrix (Fin n) (Fin n) ℂ) : Real.sqrt (hs A) = ‖A‖ := by
  rw [frobenius_norm_def, Real.sqrt_eq_rpow, hs]
  simp only [Real.rpow_two]

/- English proof (translation)
The claim follows from `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _`.
-/
theorem hs_nonneg' (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/- English proof (translation)
Rewrite using `[← sqrt_hs_eq_norm, Real.sq_sqrt (hs_nonneg' A)]`.
-/
theorem norm_sq_eq_hs (A : Matrix (Fin n) (Fin n) ℂ) : ‖A‖ ^ 2 = hs A := by
  rw [← sqrt_hs_eq_norm, Real.sq_sqrt (hs_nonneg' A)]

/- English proof (translation)
Rewrite using `[Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma re_star_mul_self_eq_norm_sq (z : ℂ) : (star z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

/- English proof (translation)
Simplify using `only [hs, trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum, re_star_mul_self_eq_norm_sq]`. Conclude with `Finset.sum_comm`.
-/
theorem hs_eq_re_trace (g : Matrix (Fin n) (Fin n) ℂ) : hs g = (trace (gᴴ * g)).re := by
  simp only [hs, trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum,
    re_star_mul_self_eq_norm_sq]
  exact Finset.sum_comm

/- English proof (translation)
Establish `hk' : kᴴ * k = 1` using `Matrix.mem_unitaryGroup_iff'.mp hk`. Rewrite using `[← sqrt_hs_eq_norm, ← sqrt_hs_eq_norm, hs_eq_re_trace, hs_eq_re_trace, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k A, hk', Matrix.one_mul]`.
-/
theorem norm_unitary_mul {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ) : ‖k * A‖ = ‖A‖ := by
  have hk' : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  rw [← sqrt_hs_eq_norm, ← sqrt_hs_eq_norm, hs_eq_re_trace, hs_eq_re_trace, conjTranspose_mul,
    Matrix.mul_assoc, ← Matrix.mul_assoc kᴴ k A, hk', Matrix.one_mul]

/- English proof (translation)
Rewrite using `[← sqrt_hs_eq_norm, hs_eq_re_trace]`. Simplify using the standard rewrite rules.
-/
theorem norm_one_eq : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = Real.sqrt n := by
  rw [← sqrt_hs_eq_norm, hs_eq_re_trace]
  simp

/- English proof (translation)
Establish `hdiag : ∑ i, ‖A i i‖ ^ 2 ≤ hs A` using `Finset.sum_le_sum fun i _ => Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)`. Establish `hsq : (∑ i, ‖A i i‖) ^ 2 ≤ (Real.sqrt n * ‖A‖) ^ 2`. Rewrite using `[mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), norm_sq_eq_hs]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.card_univ, Fintype.card_fin]`.

Conclude with `mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg n)`. Establish `h1 : ‖A.trace‖ ≤ ∑ i, ‖A i i‖` using `norm_sum_le _ _`. Establish `h2 : 0 ≤ ∑ i, ‖A i i‖` using `Finset.sum_nonneg fun _ _ => norm_nonneg _`. Establish `h3 : 0 ≤ Real.sqrt n * ‖A‖` using `mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_trace_le (A : Matrix (Fin n) (Fin n) ℂ) : ‖A.trace‖ ≤ Real.sqrt n * ‖A‖ := by
  have hdiag : ∑ i, ‖A i i‖ ^ 2 ≤ hs A :=
    Finset.sum_le_sum fun i _ =>
      Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : (∑ i, ‖A i i‖) ^ 2 ≤ (Real.sqrt n * ‖A‖) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), norm_sq_eq_hs]
    calc (∑ i, ‖A i i‖) ^ 2 ≤ (Finset.univ.card : ℝ) * ∑ i, ‖A i i‖ ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ n * hs A := by
          rw [Finset.card_univ, Fintype.card_fin]
          exact mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg n)
  have h1 : ‖A.trace‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
  have h2 : 0 ≤ ∑ i, ‖A i i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h3 : 0 ≤ Real.sqrt n * ‖A‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith

/- English proof (translation)
Establish `hk' : kᴴ * k = 1` using `Matrix.mem_unitaryGroup_iff'.mp hk`. Establish `hprod : (k - 1)ᴴ * (k - 1) = 1 + 1 - kᴴ - k`. Rewrite using `[conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hk', Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hs_eq_re_trace, hprod, trace_sub, trace_sub, trace_add, trace_one, trace_conjTranspose, Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.star_def, Complex.conj_re, Fintype.card_fin, Complex.natCast_re]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hs_unitary_sub_one {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : hs (k - 1) = 2 * n - 2 * k.trace.re := by
  have hk' : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.mp hk
  have hprod : (k - 1)ᴴ * (k - 1) = 1 + 1 - kᴴ - k := by
    rw [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hk',
      Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [hs_eq_re_trace, hprod, trace_sub, trace_sub, trace_add, trace_one, trace_conjTranspose,
    Complex.sub_re, Complex.sub_re, Complex.add_re, Complex.star_def, Complex.conj_re,
    Fintype.card_fin, Complex.natCast_re]
  ring

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => rw [pow_zero, pow_zero, one_mul, norm_one_eq]`. Consider the case `succ j ih`. Establish `hsplit : E * (k * E) ^ j = (k * E) ^ j + (E - 1) * (k * E) ^ j`. Rewrite using `[Matrix.sub_mul, Matrix.one_mul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[pow_succ', Matrix.mul_assoc, norm_unitary_mul hk, hsplit]`. Establish `hm` using `frobenius_norm_mul (E - 1) ((k * E) ^ j)`. Establish `hn0` using `norm_nonneg ((k * E) ^ j)`. Establish `hE0` using `norm_nonneg (E - 1)`.

Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul (by linarith) ih hn0 (by linarith)` to reduce the goal to its premises. Use `_ = c ^ (j + 1) * Real.sqrt n := by ring`.
-/
theorem norm_pow_le_of_unitary {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (E : Matrix (Fin n) (Fin n) ℂ) {c : ℝ}
    (hE : ‖E - 1‖ ≤ c - 1) (j : ℕ) : ‖(k * E) ^ j‖ ≤ c ^ j * Real.sqrt n := by
  induction j with
  | zero => rw [pow_zero, pow_zero, one_mul, norm_one_eq]
  | succ j ih =>
    have hsplit : E * (k * E) ^ j = (k * E) ^ j + (E - 1) * (k * E) ^ j := by
      rw [Matrix.sub_mul, Matrix.one_mul]
      abel
    rw [pow_succ', Matrix.mul_assoc, norm_unitary_mul hk, hsplit]
    have hm := frobenius_norm_mul (E - 1) ((k * E) ^ j)
    have hn0 := norm_nonneg ((k * E) ^ j)
    have hE0 := norm_nonneg (E - 1)
    calc ‖(k * E) ^ j + (E - 1) * (k * E) ^ j‖
        ≤ ‖(k * E) ^ j‖ + ‖(E - 1) * (k * E) ^ j‖ := norm_add_le _ _
      _ ≤ (1 + ‖E - 1‖) * ‖(k * E) ^ j‖ := by linarith
      _ ≤ c * (c ^ j * Real.sqrt n) := by
          apply mul_le_mul (by linarith) ih hn0 (by linarith)
      _ = c ^ (j + 1) * Real.sqrt n := by ring

/- English proof (translation)
Introduce `n k X ep hk _ hep hXe hne`. Establish `hXn : ‖X‖ ≤ ep` using `by rwa [sqrt_hs_eq_norm] at hXe`. Establish `hE1 : ‖NormedSpace.exp X - 1‖ ≤ Real.exp ep - 1`. Establish `h1` using `norm_exp_sub_one_le_exp_norm X`. Establish `h2` using `Real.exp_le_exp.mpr hXn`.

Conclude with `le_trans h1 (by linarith)`. Generalize the expression as in `NormedSpace.exp X = E at hE1 ⊢`. Establish `hpow` using `norm_pow_le_of_unitary hk E hE1`. Establish `hq : Real.exp (1 / 4) ≤ 3 / 2`. Establish `h` using `Real.abs_exp_sub_one_le (x := 1 / 4) (by norm_num [abs_of_pos])`.

Rewrite `h` using `[abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]`. Combine the linear relations using `[le_abs_self (Real.exp (1 / 4) - 1)]`. Establish `hsn : Real.sqrt n * Real.sqrt n = n` using `Real.mul_self_sqrt (Nat.cast_nonneg n)`. Use `⟨fun j hj => ?_, fun htr => ?_⟩` and prove the remaining obligations. Establish `hje : (j : ℝ) * ep ≤ 1 / 4`.

Establish `: (j : ℝ) ≤ n` using `by exact_mod_cast hj`. Use the polynomial consequences of the given equalities and inequalities. Establish `hcj : Real.exp ep ^ j ≤ 3 / 2`. Rewrite using `[← Real.exp_nat_mul]`. Conclude with `(Real.exp_le_exp.mpr hje).trans hq`.

Establish `htr` using `norm_trace_le ((k * E) ^ j)`. Establish `hb` using `hpow j`. Establish `hs0` using `Real.sqrt_nonneg (n : ℝ)`. Establish `hbound : ‖((k * E) ^ j).trace‖ ≤ n * (3 / 2)`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `[hs]`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn`. Establish `hs1 : 1 ≤ Real.sqrt n` using `Real.one_le_sqrt.mpr hn1`.

Use `set s := Real.sqrt n with hs_def`. Use `set t := Real.sqrt ep with ht_def`. Establish `ht0 : 0 ≤ t` using `Real.sqrt_nonneg _`. Establish `htt : t * t = ep` using `Real.mul_self_sqrt hep`. Establish `hst : s * t ≤ 1 / 2`.

Establish `: (s * t) * (s * t) ≤ 1 / 4`. Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities. Establish `hep1 : ep ≤ 1` using `by nlinarith`. Establish `hdel : ‖E - 1‖ ≤ 2 * ep`.

Establish `h` using `Real.abs_exp_sub_one_le (x := ep) (by rw [abs_of_nonneg hep]; exact hep1)`. Rewrite `h` using `[abs_of_nonneg hep]`. Combine the linear relations using `[le_abs_self (Real.exp ep - 1)]`. Establish `hsplit : k * E = k + k * (E - 1)`. Rewrite using `[Matrix.mul_sub, Matrix.mul_one]`.

Normalize the expressions using the abelian group laws. Establish `htrk : k.trace = n - (k * (E - 1)).trace`. Rewrite using `[← htr, hsplit, trace_add]`. Expand and normalize the polynomial expressions, which then agree. Establish `hre : (n : ℝ) - s * ‖E - 1‖ ≤ k.trace.re`.

Establish `h1` using `norm_trace_le (k * (E - 1))`. Rewrite `h1` using `[norm_unitary_mul hk, ← hs_def]`. Establish `h2` using `Complex.abs_re_le_norm (k * (E - 1)).trace`. Rewrite using `[htrk, Complex.sub_re, Complex.natCast_re]`. Combine the linear relations using `[le_abs_self (k * (E - 1)).trace.re]`.

Establish `hk1 : ‖k - 1‖ ^ 2 ≤ 4 * (s * t) ^ 2`. Rewrite using `[norm_sq_eq_hs, hs_unitary_sub_one hk]`. Establish `hE0` using `norm_nonneg (E - 1)`. Establish `: s * ‖E - 1‖ ≤ s * (2 * (t * t))`. Rewrite using `[htt]; exact mul_le_mul_of_nonneg_left hdel (by linarith)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hk1' : ‖k - 1‖ ≤ 2 * (s * t)`. Use `norm_nonneg (k - 1)` as an intermediate fact. Establish `hst0 : 0 ≤ s * t` using `mul_nonneg (by linarith) ht0`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hsum : k * E - 1 = (k - 1) + k * (E - 1)`. Rewrite using `[hsplit]`. Normalize the expressions using the abelian group laws. Rewrite using `[sqrt_hs_eq_norm, Real.sqrt_mul (Nat.cast_nonneg n), hsum]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem near_arch : ∀ (n : ℕ) (k X : Matrix (Fin n) (Fin n) ℂ) (ep : ℝ), k ∈ Matrix.unitaryGroup (Fin n) ℂ → X.IsHermitian → 0 ≤ ep → Real.sqrt (hs X) ≤ ep → n * ep ≤ 1 / 4 → (∀ j : ℕ, j ≤ n → ‖((k * NormedSpace.exp X) ^ j).trace - n‖ ≤ 3 * n) ∧ ((k * NormedSpace.exp X).trace = n → Real.sqrt (hs (k * NormedSpace.exp X - 1)) ≤ 3 * Real.sqrt (n * ep)) := by
  intro n k X ep hk _ hep hXe hne
  have hXn : ‖X‖ ≤ ep := by rwa [sqrt_hs_eq_norm] at hXe
  have hE1 : ‖NormedSpace.exp X - 1‖ ≤ Real.exp ep - 1 := by
    have h1 := norm_exp_sub_one_le_exp_norm X
    have h2 := Real.exp_le_exp.mpr hXn
    exact le_trans h1 (by linarith)
  generalize NormedSpace.exp X = E at hE1 ⊢
  have hpow := norm_pow_le_of_unitary hk E hE1
  have hq : Real.exp (1 / 4) ≤ 3 / 2 := by
    have h := Real.abs_exp_sub_one_le (x := 1 / 4) (by norm_num [abs_of_pos])
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at h
    linarith [le_abs_self (Real.exp (1 / 4) - 1)]
  have hsn : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (Nat.cast_nonneg n)
  refine ⟨fun j hj => ?_, fun htr => ?_⟩
  · have hje : (j : ℝ) * ep ≤ 1 / 4 := by
      have : (j : ℝ) ≤ n := by exact_mod_cast hj
      nlinarith
    have hcj : Real.exp ep ^ j ≤ 3 / 2 := by
      rw [← Real.exp_nat_mul]
      exact (Real.exp_le_exp.mpr hje).trans hq
    have htr := norm_trace_le ((k * E) ^ j)
    have hb := hpow j
    have hs0 := Real.sqrt_nonneg (n : ℝ)
    have hbound : ‖((k * E) ^ j).trace‖ ≤ n * (3 / 2) := by
      calc ‖((k * E) ^ j).trace‖ ≤ Real.sqrt n * ‖(k * E) ^ j‖ := htr
        _ ≤ Real.sqrt n * (Real.exp ep ^ j * Real.sqrt n) := mul_le_mul_of_nonneg_left hb hs0
        _ = (Real.sqrt n * Real.sqrt n) * Real.exp ep ^ j := by ring
        _ = n * Real.exp ep ^ j := by rw [hsn]
        _ ≤ n * (3 / 2) := mul_le_mul_of_nonneg_left hcj (Nat.cast_nonneg n)
    calc ‖((k * E) ^ j).trace - n‖ ≤ ‖((k * E) ^ j).trace‖ + ‖(n : ℂ)‖ := norm_sub_le _ _
      _ ≤ 3 * n := by rw [Complex.norm_natCast]; linarith
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hs]
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hs1 : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn1
    set s := Real.sqrt n with hs_def
    set t := Real.sqrt ep with ht_def
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have htt : t * t = ep := Real.mul_self_sqrt hep
    have hst : s * t ≤ 1 / 2 := by
      have : (s * t) * (s * t) ≤ 1 / 4 := by
        calc (s * t) * (s * t) = (s * s) * (t * t) := by ring
          _ = n * ep := by rw [hsn, htt]
          _ ≤ 1 / 4 := hne
      nlinarith
    have hep1 : ep ≤ 1 := by nlinarith
    have hdel : ‖E - 1‖ ≤ 2 * ep := by
      have h := Real.abs_exp_sub_one_le (x := ep) (by rw [abs_of_nonneg hep]; exact hep1)
      rw [abs_of_nonneg hep] at h
      linarith [le_abs_self (Real.exp ep - 1)]
    have hsplit : k * E = k + k * (E - 1) := by
      rw [Matrix.mul_sub, Matrix.mul_one]
      abel
    have htrk : k.trace = n - (k * (E - 1)).trace := by
      rw [← htr, hsplit, trace_add]
      ring
    have hre : (n : ℝ) - s * ‖E - 1‖ ≤ k.trace.re := by
      have h1 := norm_trace_le (k * (E - 1))
      rw [norm_unitary_mul hk, ← hs_def] at h1
      have h2 := Complex.abs_re_le_norm (k * (E - 1)).trace
      rw [htrk, Complex.sub_re, Complex.natCast_re]
      linarith [le_abs_self (k * (E - 1)).trace.re]
    have hk1 : ‖k - 1‖ ^ 2 ≤ 4 * (s * t) ^ 2 := by
      rw [norm_sq_eq_hs, hs_unitary_sub_one hk]
      have hE0 := norm_nonneg (E - 1)
      have : s * ‖E - 1‖ ≤ s * (2 * (t * t)) := by
        rw [htt]; exact mul_le_mul_of_nonneg_left hdel (by linarith)
      nlinarith
    have hk1' : ‖k - 1‖ ≤ 2 * (s * t) := by
      have := norm_nonneg (k - 1)
      have hst0 : 0 ≤ s * t := mul_nonneg (by linarith) ht0
      nlinarith
    have hsum : k * E - 1 = (k - 1) + k * (E - 1) := by
      rw [hsplit]
      abel
    rw [sqrt_hs_eq_norm, Real.sqrt_mul (Nat.cast_nonneg n), hsum]
    calc ‖(k - 1) + k * (E - 1)‖ ≤ ‖k - 1‖ + ‖k * (E - 1)‖ := norm_add_le _ _
      _ ≤ 2 * (s * t) + 2 * (t * t) := by rw [norm_unitary_mul hk, htt]; linarith
      _ ≤ 3 * (s * t) := by nlinarith

end NearUnitaryExp

end GlobalTheory
