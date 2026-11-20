import ReciprocityTheory.SemistableReduction.UnipotentA
import ReciprocityTheory.SemistableReduction.UnipotentB

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField Polynomial

/- English proof (translation)
Establish `hinv : Q⁻¹ * Q = 1` using `Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ)`. Establish `hinv' : Q * Q⁻¹ = 1` using `Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)`. Proceed by induction on `n with`. Consider the case `zero => simp [hinv']`. Consider the case `succ n ih`.

Rewrite using `[pow_succ, ih, pow_succ]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Q * (M ^ n * M) * Q⁻¹ := by rw [hinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]`.
-/
theorem unip_conj_pow {r : ℕ} (Q M : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.det ≠ 0) (n : ℕ) :
    (Q * M * Q⁻¹) ^ n = Q * M ^ n * Q⁻¹ := by
  have hinv : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ)
  have hinv' : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  induction n with
  | zero => simp [hinv']
  | succ n ih =>
    rw [pow_succ, ih, pow_succ]
    calc Q * M ^ n * Q⁻¹ * (Q * M * Q⁻¹) = Q * M ^ n * (Q⁻¹ * Q) * M * Q⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = Q * (M ^ n * M) * Q⁻¹ := by rw [hinv, Matrix.mul_one]; simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ), Matrix.one_mul]`.
-/
theorem unip_trace_conj {r : ℕ} (Q M : Matrix (Fin r) (Fin r) ℂ) (hQ : Q.det ≠ 0) :
    (Q * M * Q⁻¹).trace = M.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ), Matrix.one_mul]

/- English proof (translation)
Simplify using `only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]`.
-/
theorem unip_trace_map {K : Type*} [Field K] {r : ℕ} (σ : K →+* ℂ) (M : Matrix (Fin r) (Fin r) K) :
    (M.map σ).trace = σ M.trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, ih, pow_succ, Matrix.map_mul]`.
-/
theorem unip_map_pow {K : Type*} [Field K] {r : ℕ} (σ : K →+* ℂ) (M : Matrix (Fin r) (Fin r) K)
    (n : ℕ) : (M.map σ) ^ n = (M ^ n).map σ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ, Matrix.map_mul]

/- English proof (translation)
Establish `hlt : P.natDegree < r + 1` using `Nat.lt_succ_of_le hP`. Rewrite using `[Polynomial.aeval_eq_sum_range' hlt, Matrix.trace_sum, Polynomial.eval_eq_sum_range' hlt, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations. Establish `hk' : k ≤ r` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)`. Rewrite using `[Matrix.trace_smul, hγ k hk', smul_eq_mul, one_pow, mul_one, mul_comm]`.
-/
theorem unip_trace_aeval_one {K : Type*} [Field K] {r : ℕ} (γ : Matrix (Fin r) (Fin r) K)
    (hγ : ∀ k, k ≤ r → (γ ^ k).trace = r) (P : K[X]) (hP : P.natDegree ≤ r) :
    (aeval γ P).trace = r * P.eval 1 := by
  have hlt : P.natDegree < r + 1 := Nat.lt_succ_of_le hP
  rw [Polynomial.aeval_eq_sum_range' hlt, Matrix.trace_sum, Polynomial.eval_eq_sum_range' hlt,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Matrix.trace_smul, hγ k hk', smul_eq_mul, one_pow, mul_one, mul_comm]

/- English proof (translation)
Introduce `K _ _ r g γ Q hT hg hQ hA`. Use `set A : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ := fun σ => Q σ * γ.map σ * (Q σ)⁻¹ with hAdef`. Establish `hc : 0 ≤ Real.exp (2 / (3 * (r : ℝ)))` using `(Real.exp_pos _).le`. Establish `htrA : ∀ σ n, ((A σ) ^ n).trace = σ ((γ ^ n).trace)`. Introduce `σ n`.

Simplify using `only [hAdef]`. Rewrite using `[unip_conj_pow _ _ (hQ σ), unip_trace_conj _ _ (hQ σ), unip_map_pow, unip_trace_map]`. Establish `htrB : ∀ σ n, n ≤ r → ‖((A σ) ^ n).trace‖ ≤ r * Real.exp (1 / 3)`. Introduce `σ n hn`. Establish `hd : ∀ i, ‖((A σ) ^ n) i i‖ ≤ Real.exp (1 / 3)`.

Introduce `i`. Establish `h1` using `unip_diag_sq_le (A σ) _ hc (hA σ) n i`. Establish `h2 : Real.exp (2 / (3 * (r : ℝ))) ^ n ≤ Real.exp (1 / 3) ^ 2`. Rewrite using `[← Real.exp_nat_mul, ← Real.exp_nat_mul]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases. Substitute `hr` using the available equality. Establish `: n = 0` using `by omega`. Substitute `this` using the available equality. Evaluate the numerical expressions.

Establish `hr' : (0 : ℝ) < r` using `by exact_mod_cast hr`. Establish `hn' : (n : ℝ) ≤ r` using `by exact_mod_cast hn`. Combine the equalities or inequalities in the displayed calculation. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).mp (h1.trans h2)`. Combine the equalities or inequalities in the displayed calculation.

Establish `hT1 : ∀ n, 1 ≤ n → n ≤ r → (γ ^ n).trace = r`. Introduce `n h1 h2`. Take `⟨z, hz⟩` from `hT n h1 h2`. Distinguish the cases in `hz0 : z = 0`. Rewrite `hz` using `[hz0]`.

Simplify using `only [map_zero, mul_zero] at hz`. Conclude with `sub_eq_zero.mp (by simpa using hz)`. It suffices to derive a contradiction. Take `⟨σ, hσ⟩` from `NumberField.exists_conjugate_one_le_norm hz0`. Establish `e1 : σ ((γ ^ n).trace - r) = (g : ℂ) * σ z` using `by rw [hz, map_mul, map_natCast]`.

Rewrite `e1` using `[map_sub, map_natCast, ← htrA σ n]`. Establish `hn1 : ‖((A σ) ^ n).trace - r‖ ≤ r * Real.exp (1 / 3) + r`. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[Complex.norm_natCast]`. Combine the linear relations using `[htrB σ n h2]`.

Rewrite `hn1` using `[e1, norm_mul, Complex.norm_natCast]`. Establish `: (g : ℝ) ≤ g * ‖σ z‖` using `le_mul_of_one_le_right (Nat.cast_nonneg _) hσ`. Use the polynomial consequences of the given equalities and inequalities. Establish `hTall : ∀ k, k ≤ r → (γ ^ k).trace = r`. Introduce `k hk`.

Break down `Nat.eq_zero_or_pos k with h | h` into its components or cases. Substitute `h` using the available equality. Simplify using `[Matrix.trace_one]`. Conclude with `hT1 k h hk`. Establish `hN : ∀ k, 1 ≤ k → k ≤ r → ((γ - 1) ^ k).trace = 0`.

Introduce `k h1 h2`. Use `unip_trace_aeval_one γ hTall ((X - C 1) ^ k) (by rw [natDegree_pow, natDegree_X_sub_C, mul_one]; exact h2)` as an intermediate fact. Simplify using `only [map_pow, map_sub, aeval_X, map_one, eval_pow, eval_sub, eval_X, eval_one, sub_self] at this`. Rewrite using `[this, zero_pow (by omega : k ≠ 0), mul_zero]`. Use `⟨unip_pow_card_eq_zero (γ - 1) hN, fun σ => ?_⟩` and prove the remaining obligations.

Establish `hinv' : Q σ * (Q σ)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hQ σ))`. Establish `heq : Q σ * (γ.map σ - 1) * (Q σ)⁻¹ = A σ - 1`. Simplify using `only [hAdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hinv']`. Rewrite using `[heq, unip_hs_sub_one]`. Break down `Nat.eq_zero_or_pos r with hr | hr` into its components or cases.

Substitute `hr` using the available equality. Simplify using the standard rewrite rules. Establish `htr1 : (A σ).trace = r`. Establish `h7` using `htrA σ 1`. Rewrite `h7` using `[pow_one]`.

Rewrite using `[h7, hT1 1 le_rfl hr, map_natCast]`. Rewrite using `[htr1, Complex.natCast_re]`. Establish `h5` using `unip_hs_le (A σ) _ (hA σ)`. Establish `h6` using `unip_exp_bound r hr`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem unipotent_holds : UnipotentStatement := by
  intro K _ _ r g γ Q hT hg hQ hA
  set A : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ := fun σ => Q σ * γ.map σ * (Q σ)⁻¹ with hAdef
  have hc : 0 ≤ Real.exp (2 / (3 * (r : ℝ))) := (Real.exp_pos _).le
  have htrA : ∀ σ n, ((A σ) ^ n).trace = σ ((γ ^ n).trace) := by
    intro σ n
    simp only [hAdef]
    rw [unip_conj_pow _ _ (hQ σ), unip_trace_conj _ _ (hQ σ), unip_map_pow, unip_trace_map]
  have htrB : ∀ σ n, n ≤ r → ‖((A σ) ^ n).trace‖ ≤ r * Real.exp (1 / 3) := by
    intro σ n hn
    have hd : ∀ i, ‖((A σ) ^ n) i i‖ ≤ Real.exp (1 / 3) := by
      intro i
      have h1 := unip_diag_sq_le (A σ) _ hc (hA σ) n i
      have h2 : Real.exp (2 / (3 * (r : ℝ))) ^ n ≤ Real.exp (1 / 3) ^ 2 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        rcases Nat.eq_zero_or_pos r with hr | hr
        · subst hr
          have : n = 0 := by omega
          subst this; norm_num
        · have hr' : (0 : ℝ) < r := by exact_mod_cast hr
          have hn' : (n : ℝ) ≤ r := by exact_mod_cast hn
          calc (n : ℝ) * (2 / (3 * r)) = (2 / 3) * ((n : ℝ) / r) := by field_simp
            _ ≤ (2 / 3) * 1 := by gcongr; exact (div_le_one hr').mpr hn'
            _ = ((2 : ℕ) : ℝ) * (1 / 3) := by norm_num
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_pos _).le two_ne_zero).mp (h1.trans h2)
    calc ‖((A σ) ^ n).trace‖ = ‖∑ i, ((A σ) ^ n) i i‖ := rfl
      _ ≤ ∑ i, ‖((A σ) ^ n) i i‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin r, Real.exp (1 / 3) := Finset.sum_le_sum (fun i _ => hd i)
      _ = r * Real.exp (1 / 3) := by simp
  have hT1 : ∀ n, 1 ≤ n → n ≤ r → (γ ^ n).trace = r := by
    intro n h1 h2
    obtain ⟨z, hz⟩ := hT n h1 h2
    by_cases hz0 : z = 0
    · rw [hz0] at hz
      simp only [map_zero, mul_zero] at hz
      exact sub_eq_zero.mp (by simpa using hz)
    · exfalso
      obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hz0
      have e1 : σ ((γ ^ n).trace - r) = (g : ℂ) * σ z := by rw [hz, map_mul, map_natCast]
      rw [map_sub, map_natCast, ← htrA σ n] at e1
      have hn1 : ‖((A σ) ^ n).trace - r‖ ≤ r * Real.exp (1 / 3) + r := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_natCast]
        linarith [htrB σ n h2]
      rw [e1, norm_mul, Complex.norm_natCast] at hn1
      have : (g : ℝ) ≤ g * ‖σ z‖ := le_mul_of_one_le_right (Nat.cast_nonneg _) hσ
      nlinarith
  have hTall : ∀ k, k ≤ r → (γ ^ k).trace = r := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp [Matrix.trace_one]
    · exact hT1 k h hk
  have hN : ∀ k, 1 ≤ k → k ≤ r → ((γ - 1) ^ k).trace = 0 := by
    intro k h1 h2
    have := unip_trace_aeval_one γ hTall ((X - C 1) ^ k)
      (by rw [natDegree_pow, natDegree_X_sub_C, mul_one]; exact h2)
    simp only [map_pow, map_sub, aeval_X, map_one, eval_pow, eval_sub, eval_X, eval_one,
      sub_self] at this
    rw [this, zero_pow (by omega : k ≠ 0), mul_zero]
  refine ⟨unip_pow_card_eq_zero (γ - 1) hN, fun σ => ?_⟩
  have hinv' : Q σ * (Q σ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hQ σ))
  have heq : Q σ * (γ.map σ - 1) * (Q σ)⁻¹ = A σ - 1 := by
    simp only [hAdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hinv']
  rw [heq, unip_hs_sub_one]
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  have htr1 : (A σ).trace = r := by
    have h7 := htrA σ 1
    rw [pow_one] at h7
    rw [h7, hT1 1 le_rfl hr, map_natCast]
  rw [htr1, Complex.natCast_re]
  have h5 := unip_hs_le (A σ) _ (hA σ)
  have h6 := unip_exp_bound r hr
  nlinarith

end ReciprocityTheory.MultiplicativeHeights
