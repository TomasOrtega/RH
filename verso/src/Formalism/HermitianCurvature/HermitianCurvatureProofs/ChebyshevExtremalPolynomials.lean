import Formalism.HermitianCurvature.LevelRecursionCondNeeded
import Formalism.LatticeRigidity.HeightMinimum.ChebyshevLeadingCoeffHolds
import Mathlib

namespace Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials

open Finset Polynomial Formalism.FourierDecayAlt.F7

/- English proof (translation)
Simplify using `only [Formalism.SA.C.chebPt, Chebyshev.node, mul_comm Real.pi]`.
-/
lemma chebPt_eq (α β : ℝ) (n : ℕ) (j : Fin (n + 1)) :
    Formalism.SA.C.chebPt α β n j = (α + β) / 2 + (β - α) / 2 * Chebyshev.node n j := by
  simp only [Formalism.SA.C.chebPt, Chebyshev.node, mul_comm Real.pi]

/- English proof (translation)
Unfold `lagCo`. Establish `: ∀ i ∈ univ.erase j, ((c + h * x j) - (c + h * x i))⁻¹ = h⁻¹ * (x j - x i)⁻¹`. Introduce `i _`. Rewrite using `[← mul_inv]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[prod_congr rfl this, prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ j)]`. Simplify using the standard rewrite rules.
-/
lemma lagCo_affine {d : ℕ} (c h : ℝ) (x : Fin (d + 1) → ℝ) (j : Fin (d + 1)) :
    lagCo (fun i => c + h * x i) j = (h⁻¹) ^ d * lagCo x j := by
  unfold lagCo
  have : ∀ i ∈ univ.erase j, ((c + h * x j) - (c + h * x i))⁻¹ = h⁻¹ * (x j - x i)⁻¹ := by
    intro i _
    rw [← mul_inv]; congr 1; ring
  rw [prod_congr rfl this, prod_mul_distrib, prod_const, card_erase_of_mem (mem_univ j)]
  simp

noncomputable def nd (n : ℕ) (j : Fin (n + 1)) : ℝ := Chebyshev.node n j

/- English proof (translation)
Introduce `i j hij`. Use `(Chebyshev.strictAntiOn_node n).injOn (Finset.mem_coe.mpr (Finset.mem_range.mpr i.isLt)) (Finset.mem_coe.mpr (Finset.mem_range.mpr j.isLt)) hij` as an intermediate fact. Conclude with `Fin.ext this`.
-/
lemma nd_injective (n : ℕ) : Function.Injective (nd n) := by
  intro i j hij
  have := (Chebyshev.strictAntiOn_node n).injOn
    (Finset.mem_coe.mpr (Finset.mem_range.mpr i.isLt)) (Finset.mem_coe.mpr (Finset.mem_range.mpr j.isLt)) hij
  exact Fin.ext this

/- English proof (translation)
Unfold `Chebyshev.node`. Rewrite using `[Chebyshev.U_real_cos]`. Establish `: (((m:ℤ):ℝ) + 1) * (j * Real.pi / ((m + 1 : ℕ) : ℝ)) = j * Real.pi` using `by push_cast; field_simp`. Rewrite using `[this]`. Conclude with `Real.sin_nat_mul_pi j`.
-/
lemma U_mul_sin_node (m : ℕ) (j : ℕ) :
    (Chebyshev.U ℝ (m:ℤ)).eval (Chebyshev.node (m + 1) j) * Real.sin (j * Real.pi / ((m + 1 : ℕ) : ℝ)) = 0 := by
  unfold Chebyshev.node
  rw [Chebyshev.U_real_cos]
  have : (((m:ℤ):ℝ) + 1) * (j * Real.pi / ((m + 1 : ℕ) : ℝ)) = j * Real.pi := by
    push_cast; field_simp
  rw [this]
  exact Real.sin_nat_mul_pi j

/- English proof (translation)
Establish `h2 : ((2:ℝ) ^ m) ≠ 0` using `by positivity`. Establish `hmon : (X ^ 2 - 1 : ℝ[X]).Monic`. Use `monic_X_pow_sub_C (R := ℝ) (1:ℝ) (n := 2) (by norm_num)` as an intermediate fact. Simplify using `using this`. Establish `hdX : (X ^ 2 - 1 : ℝ[X]).degree = 2`.

Use `degree_X_pow_sub_C (R := ℝ) (n := 2) (by norm_num) (1:ℝ)` as an intermediate fact. Simplify using `using this`. Establish `hdL : ((X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ)).degree = ((m + 2 : ℕ) : WithBot ℕ)`. Rewrite using `[degree_mul, hdX, Chebyshev.degree_U_natCast]`. Use `norm_cast`.

Put the polynomial expressions in normal form. Establish `hdR : (C ((2:ℝ) ^ m) * Lagrange.nodal univ (nd (m + 1))).degree = ((m + 2 : ℕ) : WithBot ℕ)`. Rewrite using `[degree_C_mul h2, Lagrange.degree_nodal, card_univ, Fintype.card_fin]`. Apply `Polynomial.eq_of_degree_le_of_eval_index_eq univ (v := nd (m + 1)) ((nd_injective (m + 1)).injOn)` to reduce the goal to its premises. Rewrite using `[hdL, card_univ, Fintype.card_fin]`.

Conclude with `hdL.trans hdR.symm`. Rewrite using `[leadingCoeff_mul, hmon.leadingCoeff, Chebyshev.leadingCoeff_U_natCast, leadingCoeff_mul, leadingCoeff_C, Lagrange.nodal_monic.leadingCoeff]`. Expand and normalize the polynomial expressions, which then agree. Introduce `i _`. Rewrite using `[eval_mul, eval_mul, Lagrange.eval_nodal_at_node (mem_univ i), mul_zero]`.

Simplify using `only [eval_sub, eval_pow, eval_X, eval_one]`. Establish `h` using `U_mul_sin_node m i`. Establish `hs : (nd (m + 1) i) ^ 2 - 1 = - Real.sin (i * Real.pi / ((m + 1 : ℕ) : ℝ)) ^ 2`. Use `Real.sin_sq_add_cos_sq ((i:ℕ) * Real.pi / ((m + 1 : ℕ) : ℝ))` as an intermediate fact. Unfold `nd Chebyshev.node`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[hs]`. Unfold `nd`. Take the linear combination `(- Real.sin (i * Real.pi / ((m + 1 : ℕ) : ℝ))) * h`.
-/
lemma nodal_eq (m : ℕ) :
    (X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ) = C ((2:ℝ) ^ m) * Lagrange.nodal univ (nd (m + 1)) := by
  have h2 : ((2:ℝ) ^ m) ≠ 0 := by positivity
  have hmon : (X ^ 2 - 1 : ℝ[X]).Monic := by
    have := monic_X_pow_sub_C (R := ℝ) (1:ℝ) (n := 2) (by norm_num)
    simpa using this
  have hdX : (X ^ 2 - 1 : ℝ[X]).degree = 2 := by
    have := degree_X_pow_sub_C (R := ℝ) (n := 2) (by norm_num) (1:ℝ)
    simpa using this
  have hdL : ((X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ)).degree = ((m + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, hdX, Chebyshev.degree_U_natCast]
    norm_cast; ring_nf
  have hdR : (C ((2:ℝ) ^ m) * Lagrange.nodal univ (nd (m + 1))).degree = ((m + 2 : ℕ) : WithBot ℕ) := by
    rw [degree_C_mul h2, Lagrange.degree_nodal, card_univ, Fintype.card_fin]
  apply Polynomial.eq_of_degree_le_of_eval_index_eq univ (v := nd (m + 1))
    ((nd_injective (m + 1)).injOn)
  · rw [hdL, card_univ, Fintype.card_fin]
  · exact hdL.trans hdR.symm
  · rw [leadingCoeff_mul, hmon.leadingCoeff, Chebyshev.leadingCoeff_U_natCast, leadingCoeff_mul,
        leadingCoeff_C, Lagrange.nodal_monic.leadingCoeff]; ring
  · intro i _
    rw [eval_mul, eval_mul, Lagrange.eval_nodal_at_node (mem_univ i), mul_zero]
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    have h := U_mul_sin_node m i
    have hs : (nd (m + 1) i) ^ 2 - 1 = - Real.sin (i * Real.pi / ((m + 1 : ℕ) : ℝ)) ^ 2 := by
      have := Real.sin_sq_add_cos_sq ((i:ℕ) * Real.pi / ((m + 1 : ℕ) : ℝ))
      unfold nd Chebyshev.node
      linarith
    rw [hs]
    unfold nd
    linear_combination (- Real.sin (i * Real.pi / ((m + 1 : ℕ) : ℝ))) * h

/- English proof (translation)
Establish `h` using `Chebyshev.add_one_mul_T_eq_poly_in_U (R := ℝ) (m:ℤ)`. Rewrite using `[derivative_mul]`. Simplify using `only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, map_ofNat]`. Move the coercions through the operations in `at h`. Take the linear combination `-h`.
-/
lemma deriv_eq (m : ℕ) :
    derivative ((X ^ 2 - 1) * Chebyshev.U ℝ (m:ℤ)) =
      ((m:ℝ[X]) + 1) * Chebyshev.T ℝ ((m:ℤ) + 1) + X * Chebyshev.U ℝ (m:ℤ) := by
  have h := Chebyshev.add_one_mul_T_eq_poly_in_U (R := ℝ) (m:ℤ)
  rw [derivative_mul]
  simp only [derivative_sub, derivative_X_pow, derivative_one, sub_zero, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, map_ofNat]
  push_cast at h
  linear_combination -h

/- English proof (translation)
Distinguish the cases in `h0 : (j:ℕ) = 0`. Establish `: nd (m + 1) j = 1` using `by unfold nd; rw [h0]; exact Chebyshev.node_eq_one`. Rewrite using `[this, if_pos (Or.inl h0), h0, Chebyshev.U_eval_one]`. Simplify using the standard rewrite rules. Distinguish the cases in `h1 : (j:ℕ) = m + 1`.

Establish `: nd (m + 1) j = -1` using `by unfold nd; rw [h1]; exact Chebyshev.node_eq_neg_one (by omega)`. Rewrite using `[this, if_pos (Or.inr h1), h1, Chebyshev.U_eval_neg_one, Int.cast_negOnePow]`. Use `push_cast`. Rewrite using `[zpow_natCast, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[if_neg (by tauto)]`. Establish `h` using `U_mul_sin_node m j`. Establish `hpos : 0 < Real.sin ((j:ℕ) * Real.pi / ((m + 1 : ℕ) : ℝ))`. Establish `hj : (0:ℝ) < (j:ℕ)` using `by exact_mod_cast Nat.pos_of_ne_zero h0`. Establish `hjm : ((j:ℕ):ℝ) < ((m + 1 : ℕ) : ℝ)`.

Use `j.isLt` as an intermediate fact. Conclude with `(by omega : (j:ℕ) < m + 1)` after adjusting the coercions. Establish `hm : (0:ℝ) < ((m + 1 : ℕ) : ℝ)` using `by positivity`. Apply `Real.sin_pos_of_pos_of_lt_pi` to reduce the goal to its premises. Use `Real.pi_pos` as an intermediate fact.

Check the signs of the components of the expression. Rewrite using `[div_lt_iff₀ hm, mul_comm]`. Conclude with `mul_lt_mul_of_pos_left hjm Real.pi_pos`. Establish `: (Chebyshev.U ℝ (m:ℤ)).eval (nd (m + 1) j) = 0`. Break down `mul_eq_zero.mp h with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h hpos.ne'`. Rewrite using `[this, mul_zero]`.
-/
lemma node_mul_U (m : ℕ) (j : Fin (m + 2)) :
    nd (m + 1) j * (Chebyshev.U ℝ (m:ℤ)).eval (nd (m + 1) j) =
      if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (-1) ^ (j:ℕ) * ((m:ℝ) + 1) else 0 := by
  by_cases h0 : (j:ℕ) = 0
  · have : nd (m + 1) j = 1 := by unfold nd; rw [h0]; exact Chebyshev.node_eq_one
    rw [this, if_pos (Or.inl h0), h0, Chebyshev.U_eval_one]; simp
  by_cases h1 : (j:ℕ) = m + 1
  · have : nd (m + 1) j = -1 := by unfold nd; rw [h1]; exact Chebyshev.node_eq_neg_one (by omega)
    rw [this, if_pos (Or.inr h1), h1, Chebyshev.U_eval_neg_one, Int.cast_negOnePow]
    push_cast
    rw [zpow_natCast, pow_succ]; ring
  · rw [if_neg (by tauto)]
    have h := U_mul_sin_node m j
    have hpos : 0 < Real.sin ((j:ℕ) * Real.pi / ((m + 1 : ℕ) : ℝ)) := by
      have hj : (0:ℝ) < (j:ℕ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have hjm : ((j:ℕ):ℝ) < ((m + 1 : ℕ) : ℝ) := by
        have := j.isLt
        exact_mod_cast (by omega : (j:ℕ) < m + 1)
      have hm : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      apply Real.sin_pos_of_pos_of_lt_pi
      · have := Real.pi_pos; positivity
      · rw [div_lt_iff₀ hm, mul_comm]
        exact mul_lt_mul_of_pos_left hjm Real.pi_pos
    have : (Chebyshev.U ℝ (m:ℤ)).eval (nd (m + 1) j) = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · exact h
      · exact absurd h hpos.ne'
    rw [this, mul_zero]

/- English proof (translation)
Establish `h1` using `congrArg (fun p => eval (nd (m + 1) j) (derivative p)) (nodal_eq m)`. Simplify using `only [deriv_eq, derivative_C_mul, eval_mul, eval_C, eval_add, eval_X, eval_natCast, eval_one, Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ j), Lagrange.eval_nodal] at h1`. Rewrite using `[← h1, node_mul_U]`. Establish `hT : (Chebyshev.T ℝ ((m:ℤ) + 1)).eval (nd (m + 1) j) = (-1) ^ (j:ℕ)`. Use `Chebyshev.eval_T_real_node (n := m + 1) (i := j) (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt))` as an intermediate fact.

Move the coercions through the operations in `at this`. Conclude with `this`. Rewrite using `[hT]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
lemma prod_node (m : ℕ) (j : Fin (m + 2)) :
    (2:ℝ) ^ m * ∏ i ∈ univ.erase j, (nd (m + 1) j - nd (m + 1) i) =
      (-1) ^ (j:ℕ) * ((m:ℝ) + 1) * (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then 2 else 1) := by
  have h1 := congrArg (fun p => eval (nd (m + 1) j) (derivative p)) (nodal_eq m)
  simp only [deriv_eq, derivative_C_mul, eval_mul, eval_C, eval_add, eval_X, eval_natCast, eval_one,
    Lagrange.eval_nodal_derivative_eval_node_eq (mem_univ j), Lagrange.eval_nodal] at h1
  rw [← h1, node_mul_U]
  have hT : (Chebyshev.T ℝ ((m:ℤ) + 1)).eval (nd (m + 1) j) = (-1) ^ (j:ℕ) := by
    have := Chebyshev.eval_T_real_node (n := m + 1) (i := j) (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt))
    push_cast at this
    exact this
  rw [hT]
  split_ifs <;> ring

/- English proof (translation)
Establish `h` using `prod_node m j`. Unfold `lagCo`. Rewrite using `[prod_inv_distrib]`. Establish `h2 : (2:ℝ) ^ m ≠ 0` using `by positivity`. Establish `hm : (m:ℝ) + 1 ≠ 0` using `by positivity`.

Establish `hs : ((-1:ℝ) ^ (j:ℕ)) * ((-1:ℝ) ^ (j:ℕ)) = 1`. Rewrite using `[← mul_pow]`. Simplify using the standard rewrite rules. Establish `hs0 : ((-1:ℝ) ^ (j:ℕ)) ≠ 0` using `by positivity`. Establish `hP : ∏ i ∈ univ.erase j, (nd (m + 1) j - nd (m + 1) i) = (-1) ^ (j:ℕ) * ((m:ℝ) + 1) * (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then 2 else 1) / (2:ℝ) ^ m`.

Rewrite using `[← h]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hP]`. Use `split_ifs`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `-hs`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hs`.
-/
lemma lagCo_nd (m : ℕ) (j : Fin (m + 2)) :
    lagCo (nd (m + 1)) j =
      (-1) ^ (j:ℕ) * (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then 1 / 2 else 1) * ((2:ℝ) ^ m / ((m:ℝ) + 1)) := by
  have h := prod_node m j
  unfold lagCo
  rw [prod_inv_distrib]
  have h2 : (2:ℝ) ^ m ≠ 0 := by positivity
  have hm : (m:ℝ) + 1 ≠ 0 := by positivity
  have hs : ((-1:ℝ) ^ (j:ℕ)) * ((-1:ℝ) ^ (j:ℕ)) = 1 := by
    rw [← mul_pow]; simp
  have hs0 : ((-1:ℝ) ^ (j:ℕ)) ≠ 0 := by positivity
  have hP : ∏ i ∈ univ.erase j, (nd (m + 1) j - nd (m + 1) i) =
      (-1) ^ (j:ℕ) * ((m:ℝ) + 1) * (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then 2 else 1) / (2:ℝ) ^ m := by
    rw [← h]; field_simp
  rw [hP]
  split_ifs
  · field_simp; linear_combination -hs
  · field_simp; linear_combination -hs

/- English proof (translation)
Introduce `α β n hαβ hn j`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Establish `hd : 0 < β - α` using `by linarith`. Establish `e : Formalism.SA.C.chebPt α β (m + 1) = fun i => (α + β) / 2 + (β - α) / 2 * nd (m + 1) i`. Use function extensionality and compare the values at `i`.

Conclude with `chebPt_eq α β (m + 1) i`. Rewrite using `[e, lagCo_affine, lagCo_nd]`. Establish `: ((β - α) / 2)⁻¹ = 2 / (β - α)` using `by rw [inv_div]`. Rewrite using `[this, Nat.add_sub_cancel]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coValue : Formalism.FourierDecayAlt.F7.ChebCoValue := by
  intro α β n hαβ hn j
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hd : 0 < β - α := by linarith
  have e : Formalism.SA.C.chebPt α β (m + 1) = fun i => (α + β) / 2 + (β - α) / 2 * nd (m + 1) i := by
    funext i; exact chebPt_eq α β (m + 1) i
  rw [e, lagCo_affine, lagCo_nd]
  have : ((β - α) / 2)⁻¹ = 2 / (β - α) := by rw [inv_div]
  rw [this, Nat.add_sub_cancel]
  push_cast
  ring

/- English proof (translation)
Rewrite using `[Fin.sum_univ_succ, Fin.sum_univ_castSucc]`. Establish `: ∀ i : Fin m, (if ((i.castSucc.succ : Fin (m + 2)) : ℕ) = 0 ∨ ((i.castSucc.succ : Fin (m + 2)) : ℕ) = m + 1 then (1 / 2 : ℝ) else 1) = 1`. Introduce `i`. Rewrite using `[if_neg]`. Use `i.isLt` as an intermediate fact.

Simplify using `only [Fin.val_succ, Fin.val_castSucc]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[sum_congr rfl (fun i _ => this i)]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_half (m : ℕ) :
    ∑ j : Fin (m + 2), (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) = (m:ℝ) + 1 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have : ∀ i : Fin m, (if ((i.castSucc.succ : Fin (m + 2)) : ℕ) = 0 ∨
      ((i.castSucc.succ : Fin (m + 2)) : ℕ) = m + 1 then (1 / 2 : ℝ) else 1) = 1 := by
    intro i
    rw [if_neg]
    have := i.isLt
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  rw [sum_congr rfl (fun i _ => this i)]
  simp
  ring

/- English proof (translation)
Introduce `α β n hαβ hn`. Establish `hd : 0 < β - α` using `by linarith`. Prove the components needed by the constructor for the conclusion. Introduce `i j hij`. Rewrite `hij` using `[chebPt_eq, chebPt_eq]`.

Establish `h2 : Chebyshev.node n i = Chebyshev.node n j`. Establish `: (β - α) / 2 * Chebyshev.node n i = (β - α) / 2 * Chebyshev.node n j` using `by linarith`. Conclude with `mul_left_cancel₀ (by positivity) this`. Conclude with `nd_injective n h2`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`.

Establish `hv : ∀ j : Fin (m + 2), |lagCo (Formalism.SA.C.chebPt α β (m + 1)) j| = (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) * (((2 : ℝ) ^ m / ((m:ℝ) + 1)) * (2 / (β - α)) ^ (m + 1))`. Introduce `j`. Rewrite using `[coValue α β (m + 1) hαβ hn j, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.add_sub_cancel]`. Establish `h1 : |(if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1)| = (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1)`. Apply the tactic sequence `apply abs_of_nonneg; split_ifs <;> norm_num`.

Rewrite using `[h1, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[sum_congr rfl (fun j _ => hv j), ← sum_mul, sum_half]`. Establish `hm : (m:ℝ) + 1 ≠ 0` using `by positivity`.

Rewrite using `[show (4:ℝ) / (β - α) = 2 * (2 / (β - α)) by ring, mul_pow, pow_succ (2:ℝ) m]`. Clear the denominators using the available nonvanishing facts.
-/
theorem sharp : Formalism.FourierDecayAlt.F7.ChebSharp := by
  intro α β n hαβ hn
  have hd : 0 < β - α := by linarith
  constructor
  · intro i j hij
    rw [chebPt_eq, chebPt_eq] at hij
    have h2 : Chebyshev.node n i = Chebyshev.node n j := by
      have : (β - α) / 2 * Chebyshev.node n i = (β - α) / 2 * Chebyshev.node n j := by linarith
      exact mul_left_cancel₀ (by positivity) this
    exact nd_injective n h2
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hv : ∀ j : Fin (m + 2), |lagCo (Formalism.SA.C.chebPt α β (m + 1)) j| =
        (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) *
          (((2 : ℝ) ^ m / ((m:ℝ) + 1)) * (2 / (β - α)) ^ (m + 1)) := by
      intro j
      rw [coValue α β (m + 1) hαβ hn j, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
        one_mul, Nat.add_sub_cancel]
      have h1 : |(if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1)| =
          (if (j:ℕ) = 0 ∨ (j:ℕ) = m + 1 then (1 / 2 : ℝ) else 1) := by
        apply abs_of_nonneg; split_ifs <;> norm_num
      rw [h1, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      push_cast; ring
    rw [sum_congr rfl (fun j _ => hv j), ← sum_mul, sum_half]
    have hm : (m:ℝ) + 1 ≠ 0 := by positivity
    rw [show (4:ℝ) / (β - α) = 2 * (2 / (β - α)) by ring, mul_pow, pow_succ (2:ℝ) m]
    field_simp

/- English proof (translation)
Establish `hlt : ((X : ℝ[X]) ^ k).degree < (univ : Finset (Fin (d + 1))).card`. Rewrite using `[degree_X_pow, card_univ, Fintype.card_fin]`. Conclude with `Nat.lt_succ_of_le hk` after adjusting the coercions. Establish `h` using `Lagrange.coeff_eq_sum (s := univ) (v := y) hy.injOn hlt`. Simplify using `only [card_univ, Fintype.card_fin, Nat.add_sub_cancel, coeff_X_pow, eval_pow, eval_X] at h`.

Establish `e : (if k = d then (1:ℝ) else 0) = if d = k then 1 else 0`. Distinguish the cases in `hkd : k = d`. Substitute `hkd` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hkd, if_neg (Ne.symm hkd)]`.

Rewrite using `[e, h]`. Use `sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Unfold `lagCo`. Rewrite using `[prod_inv_distrib, div_eq_mul_inv, mul_comm]`.
-/
lemma sum_lagCo_mul_pow {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (k : ℕ)
    (hk : k ≤ d) : ∑ j, lagCo y j * y j ^ k = if k = d then 1 else 0 := by
  have hlt : ((X : ℝ[X]) ^ k).degree < (univ : Finset (Fin (d + 1))).card := by
    rw [degree_X_pow, card_univ, Fintype.card_fin]; exact_mod_cast Nat.lt_succ_of_le hk
  have h := Lagrange.coeff_eq_sum (s := univ) (v := y) hy.injOn hlt
  simp only [card_univ, Fintype.card_fin, Nat.add_sub_cancel, coeff_X_pow, eval_pow, eval_X] at h
  have e : (if k = d then (1:ℝ) else 0) = if d = k then 1 else 0 := by
    by_cases hkd : k = d
    · subst hkd; simp
    · rw [if_neg hkd, if_neg (Ne.symm hkd)]
  rw [e, h]
  refine sum_congr rfl fun i _ => ?_
  unfold lagCo
  rw [prod_inv_distrib, div_eq_mul_inv, mul_comm]

/- English proof (translation)
Repeatedly rewrite using `[smul_sum, smul_smul]`. Rewrite using `[sum_comm]`. Repeatedly rewrite using `[← sum_smul]`. Establish `: ∀ k : Fin (d + 1), (∑ j, ((lagCo y j : ℝ) : ℂ) * (y j : ℂ) ^ (k:ℕ)) = if k = Fin.last d then 1 else 0`. Introduce `k`.

Establish `h` using `sum_lagCo_mul_pow y hy k (Nat.lt_succ_iff.mp k.isLt)`. Establish `h'` using `congrArg (fun r : ℝ => (r : ℂ)) h`. Move the coercions through the operations in `at h'`. Rewrite using `[h']`. Distinguish the cases in `hk : k = Fin.last d`.

Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Establish `hk' : ¬ ((k:ℕ) = d)` using `fun h0 => hk (Fin.ext (by simpa using h0))`. Rewrite using `[if_neg hk, if_neg hk']`. Simplify using the standard rewrite rules.

Repeatedly rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
lemma lead_complex {V : Type} [AddCommGroup V] [Module ℂ V] {d : ℕ} (y : Fin (d + 1) → ℝ)
    (hy : Function.Injective y) (a : Fin (d + 1) → V) :
    a (Fin.last d) = ∑ j, ((lagCo y j : ℝ) : ℂ) • ∑ k : Fin (d + 1), ((y j : ℂ) ^ (k : ℕ)) • a k := by
  simp_rw [smul_sum, smul_smul]
  rw [sum_comm]
  simp_rw [← sum_smul]
  have : ∀ k : Fin (d + 1), (∑ j, ((lagCo y j : ℝ) : ℂ) * (y j : ℂ) ^ (k:ℕ)) =
      if k = Fin.last d then 1 else 0 := by
    intro k
    have h := sum_lagCo_mul_pow y hy k (Nat.lt_succ_iff.mp k.isLt)
    have h' := congrArg (fun r : ℝ => (r : ℂ)) h
    push_cast at h'
    rw [h']
    by_cases hk : k = Fin.last d
    · subst hk; simp
    · have hk' : ¬ ((k:ℕ) = d) := fun h0 => hk (Fin.ext (by simpa using h0))
      rw [if_neg hk, if_neg hk']; simp
  simp_rw [this]
  simp

/- English proof (translation)
Introduce `V _ _ α β n a B hαβ hn hB`. Take `⟨hinj, hsum⟩` from `sharp α β n hαβ hn`. Rewrite using `[lead_complex _ hinj a, ← hsum, sum_mul]`. Use `(norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul, Complex.norm_real, Real.norm_eq_abs]`.

Conclude with `mul_le_mul_of_nonneg_left (hB j) (abs_nonneg _)`.
-/
theorem leadBound : Formalism.FourierDecayAlt.F7.ChebLeadBound := by
  intro V _ _ α β n a B hαβ hn hB
  obtain ⟨hinj, hsum⟩ := sharp α β n hαβ hn
  rw [lead_complex _ hinj a, ← hsum, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun j _ => ?_)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB j) (abs_nonneg _)

/- English proof (translation)
Rewrite using `[prod_range_add, prod_range_succ, if_pos rfl, mul_one]`. Use `congr 1`. Rewrite using `[← prod_range_reflect, ← prod_range_add_one_eq_factorial]`. Use `push_cast`. Use `prod_congr rfl fun i hi => ?_` and prove the remaining obligations.

Establish `hi' : i < j` using `mem_range.mp hi`. Rewrite using `[if_neg (by omega)]`. Establish `: ((j - 1 - i : ℕ) : ℝ) = (j:ℝ) - 1 - i`. Rewrite using `[Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp`. Rewrite using `[this, abs_of_nonneg (by ring_nf; positivity)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← prod_range_add_one_eq_factorial]`. Use `push_cast`. Use `prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg (by omega)]`.

Rewrite using `[abs_sub_comm, abs_of_nonneg (by ring_nf; positivity)]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma prod_abs_int (j k : ℕ) :
    ∏ i ∈ range (j + 1 + k), (if i = j then (1:ℝ) else |(j:ℝ) - i|) = j.factorial * k.factorial := by
  rw [prod_range_add, prod_range_succ, if_pos rfl, mul_one]
  congr 1
  · rw [← prod_range_reflect, ← prod_range_add_one_eq_factorial]
    push_cast
    refine prod_congr rfl fun i hi => ?_
    have hi' : i < j := mem_range.mp hi
    rw [if_neg (by omega)]
    have : ((j - 1 - i : ℕ) : ℝ) = (j:ℝ) - 1 - i := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    rw [this, abs_of_nonneg (by ring_nf; positivity)]
    ring
  · rw [← prod_range_add_one_eq_factorial]
    push_cast
    refine prod_congr rfl fun i _ => ?_
    rw [if_neg (by omega)]
    rw [abs_sub_comm, abs_of_nonneg (by ring_nf; positivity)]
    ring

/- English proof (translation)
The claim follows from `|lagCo (fun i : Fin (n + 1) => ((i:ℕ):ℝ)) j| = ((j:ℕ).factorial * (n - (j:ℕ)).factorial : ℝ)⁻¹ := by unfold lagCo rw [prod_inv_distrib, abs_inv, abs_prod] congr 1 have h1 : ∏ i ∈ univ.erase j, |(((j:ℕ):ℝ)) - ((i:ℕ):ℝ)| = ∏ i : Fin (n + 1), (if (i:ℕ) = (j:ℕ) then (1:ℝ) else |((j:ℕ …`.
-/
lemma abs_lagCo_nat (n : ℕ) (j : Fin (n + 1)) :
    |lagCo (fun i : Fin (n + 1) => ((i:ℕ):ℝ)) j| =
      ((j:ℕ).factorial * (n - (j:ℕ)).factorial : ℝ)⁻¹ := by
  unfold lagCo
  rw [prod_inv_distrib, abs_inv, abs_prod]
  congr 1
  have h1 : ∏ i ∈ univ.erase j, |(((j:ℕ):ℝ)) - ((i:ℕ):ℝ)| =
      ∏ i : Fin (n + 1), (if (i:ℕ) = (j:ℕ) then (1:ℝ) else |((j:ℕ):ℝ) - ((i:ℕ):ℝ)|) := by
    rw [← mul_prod_erase univ _ (mem_univ j), if_pos rfl, one_mul]
    refine prod_congr rfl fun i hi => ?_
    rw [if_neg (fun h => (mem_erase.mp hi).1 (Fin.ext h))]
  rw [h1, Fin.prod_univ_eq_prod_range (fun i => if i = (j:ℕ) then (1:ℝ) else |((j:ℕ):ℝ) - (i:ℝ)|) (n + 1)]
  have hj := j.isLt
  have e : n + 1 = (j:ℕ) + 1 + (n - (j:ℕ)) := by omega
  have h2 := prod_abs_int (j:ℕ) (n - (j:ℕ))
  rw [← e] at h2
  exact h2

/- English proof (translation)
Introduce `n y₀ h hh`. Establish `e : (fun i : Fin (n + 1) => y₀ + ((i:ℕ):ℝ) * h) = fun i : Fin (n + 1) => y₀ + h * ((i:ℕ):ℝ)`. Use function extensionality and compare the values at `i`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Repeatedly rewrite using `[lagCo_affine, abs_mul, abs_lagCo_nat]`. Rewrite using `[← mul_sum, abs_of_nonneg (by positivity)]`. Establish `hs : ∑ j : Fin (n + 1), (((j:ℕ).factorial * (n - (j:ℕ)).factorial : ℝ))⁻¹ = 2 ^ n / (n.factorial : ℝ)`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun j => ((j.factorial * (n - j).factorial : ℝ))⁻¹) (n + 1)]`. Establish `hf : (n.factorial : ℝ) ≠ 0` using `by exact_mod_cast n.factorial_ne_zero`.

Rewrite using `[eq_div_iff hf, sum_mul]`. Use `Nat.sum_range_choose n` as an intermediate fact. Establish `h2 : ((∑ m ∈ range (n + 1), n.choose m : ℕ) : ℝ) = 2 ^ n` using `by rw [this]; push_cast; rfl`. Rewrite using `[← h2]`. Use `push_cast`.

Use `sum_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `hj' : j ≤ n` using `Nat.lt_succ_iff.mp (mem_range.mp hj)`. Establish `hc` using `Nat.choose_mul_factorial_mul_factorial hj'`. Establish `hc' : (n.choose j : ℝ) * j.factorial * (n - j).factorial = n.factorial` using `by exact_mod_cast hc`. Establish `h1 : (j.factorial : ℝ) ≠ 0` using `by exact_mod_cast j.factorial_ne_zero`.

Establish `h3 : ((n - j).factorial : ℝ) ≠ 0` using `by exact_mod_cast (n - j).factorial_ne_zero`. Rewrite using `[← hc']`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hs, div_pow, inv_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem equiCo : Formalism.FourierDecayAlt.F7.EquiCo := by
  intro n y₀ h hh
  have e : (fun i : Fin (n + 1) => y₀ + ((i:ℕ):ℝ) * h) =
      fun i : Fin (n + 1) => y₀ + h * ((i:ℕ):ℝ) := by
    funext i; ring
  rw [e]
  simp_rw [lagCo_affine, abs_mul, abs_lagCo_nat]
  rw [← mul_sum, abs_of_nonneg (by positivity)]
  have hs : ∑ j : Fin (n + 1), (((j:ℕ).factorial * (n - (j:ℕ)).factorial : ℝ))⁻¹ =
      2 ^ n / (n.factorial : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => ((j.factorial * (n - j).factorial : ℝ))⁻¹) (n + 1)]
    have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [eq_div_iff hf, sum_mul]
    have := Nat.sum_range_choose n
    have h2 : ((∑ m ∈ range (n + 1), n.choose m : ℕ) : ℝ) = 2 ^ n := by rw [this]; push_cast; rfl
    rw [← h2]
    push_cast
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
    have hc := Nat.choose_mul_factorial_mul_factorial hj'
    have hc' : (n.choose j : ℝ) * j.factorial * (n - j).factorial = n.factorial := by exact_mod_cast hc
    have h1 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    have h3 : ((n - j).factorial : ℝ) ≠ 0 := by exact_mod_cast (n - j).factorial_ne_zero
    rw [← hc']; field_simp
  rw [hs, div_pow, inv_pow]
  ring

/- English proof (translation)
Introduce `α β n hαβ hn j`. Establish `hnpos : (0:ℝ) < n` using `by exact_mod_cast hn`. Establish `h` using `Formalism.SA.P.node_sub_node_ge (n := n) (i := j) (k := j + 1) hn (Nat.lt_succ_self _) j.isLt`. Rewrite using `[chebPt_eq, chebPt_eq, abs_sub_comm]`. Simplify using `only [Fin.val_succ, Fin.val_castSucc]`.

Establish `e : ((((j:ℕ) + 1 : ℕ) : ℝ) - (j:ℕ)) = 1` using `by push_cast; ring`. Rewrite `h` using `[e]`. Establish `h2 : (β - α) / (n:ℝ) ^ 2 = (β - α) / 2 * (2 * 1 ^ 2 / (n:ℝ) ^ 2)` using `by ring`. Establish `h3 : (β - α) / 2 * (2 * 1 ^ 2 / (n:ℝ) ^ 2) ≤ (β - α) / 2 * (Chebyshev.node n j - Chebyshev.node n (j + 1))` using `mul_le_mul_of_nonneg_left h (by linarith)`. Rewrite using `[h2]`.

Use `h3.trans ((le_abs_self _).trans (le_of_eq ?_))` and prove the remaining obligations. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem spacing : Formalism.FourierDecayAlt.F7.ChebSpacing := by
  intro α β n hαβ hn j
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have h := Formalism.SA.P.node_sub_node_ge (n := n) (i := j) (k := j + 1) hn (Nat.lt_succ_self _) j.isLt
  rw [chebPt_eq, chebPt_eq, abs_sub_comm]
  simp only [Fin.val_succ, Fin.val_castSucc]
  have e : ((((j:ℕ) + 1 : ℕ) : ℝ) - (j:ℕ)) = 1 := by push_cast; ring
  rw [e] at h
  have h2 : (β - α) / (n:ℝ) ^ 2 = (β - α) / 2 * (2 * 1 ^ 2 / (n:ℝ) ^ 2) := by ring
  have h3 : (β - α) / 2 * (2 * 1 ^ 2 / (n:ℝ) ^ 2) ≤
      (β - α) / 2 * (Chebyshev.node n j - Chebyshev.node n (j + 1)) :=
    mul_le_mul_of_nonneg_left h (by linarith)
  rw [h2]
  refine h3.trans ((le_abs_self _).trans (le_of_eq ?_))
  congr 1; ring

/- English proof (translation)
Introduce `n L hn hL`. Establish `hnpos : (0:ℝ) < n` using `by exact_mod_cast hn`. Establish `hLpos : 0 < L` using `lt_of_lt_of_le hnpos hL`. Establish `h1 : (1:ℝ) ≤ L / n` using `by rw [le_div_iff₀ hnpos]; linarith`. Establish `hfl : (1:ℤ) ≤ ⌊L / (n:ℝ)⌋` using `Int.le_floor.mpr (by exact_mod_cast h1)`.

Use `set h : ℝ := ((⌊L / (n:ℝ)⌋ : ℤ) : ℝ) with hh`. Establish `hh1 : (1:ℝ) ≤ h` using `by rw [hh]; exact_mod_cast hfl`. Establish `hlt : L / n < h + 1` using `Int.lt_floor_add_one _`. Establish `hpos : 0 < h` using `by linarith`. Establish `h2 : 2 / h ≤ 4 * n / L`.

Rewrite using `[div_le_div_iff₀ hpos hLpos]`. Establish `: L < (h + 1) * n` using `by rwa [div_lt_iff₀ hnpos] at hlt`. Use the polynomial consequences of the given equalities and inequalities. Establish `h3 : (2 / h) ^ n ≤ (4 * n / L) ^ n` using `pow_le_pow_left₀ (by positivity) h2 n`. Establish `hf : (0:ℝ) < n.factorial` using `by exact_mod_cast n.factorial_pos`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[show 4 * (n:ℝ) / L = 4 / L * n by ring, mul_pow]; ring`. Use `_ ≤ (4 / L) ^ n * Real.exp n := by gcongr`. Conclude with `Real.pow_div_factorial_le_exp _ hnpos.le n`. Use `_ = (4 * Real.exp 1 / L) ^ n := by`.

Rewrite using `[show 4 * Real.exp 1 / L = 4 / L * Real.exp 1 by ring, mul_pow, ← Real.exp_nat_mul, mul_one]`.
-/
theorem equiCoBound : Formalism.FourierDecayAlt.F7.EquiCoBound := by
  intro n L hn hL
  have hnpos : (0:ℝ) < n := by exact_mod_cast hn
  have hLpos : 0 < L := lt_of_lt_of_le hnpos hL
  have h1 : (1:ℝ) ≤ L / n := by rw [le_div_iff₀ hnpos]; linarith
  have hfl : (1:ℤ) ≤ ⌊L / (n:ℝ)⌋ := Int.le_floor.mpr (by exact_mod_cast h1)
  set h : ℝ := ((⌊L / (n:ℝ)⌋ : ℤ) : ℝ) with hh
  have hh1 : (1:ℝ) ≤ h := by rw [hh]; exact_mod_cast hfl
  have hlt : L / n < h + 1 := Int.lt_floor_add_one _
  have hpos : 0 < h := by linarith
  have h2 : 2 / h ≤ 4 * n / L := by
    rw [div_le_div_iff₀ hpos hLpos]
    have : L < (h + 1) * n := by rwa [div_lt_iff₀ hnpos] at hlt
    nlinarith
  have h3 : (2 / h) ^ n ≤ (4 * n / L) ^ n := pow_le_pow_left₀ (by positivity) h2 n
  have hf : (0:ℝ) < n.factorial := by exact_mod_cast n.factorial_pos
  calc (2 / h) ^ n / (n.factorial : ℝ) ≤ (4 * n / L) ^ n / (n.factorial : ℝ) := by gcongr
    _ = (4 / L) ^ n * ((n:ℝ) ^ n / n.factorial) := by
        rw [show 4 * (n:ℝ) / L = 4 / L * n by ring, mul_pow]; ring
    _ ≤ (4 / L) ^ n * Real.exp n := by
        gcongr
        exact Real.pow_div_factorial_le_exp _ hnpos.le n
    _ = (4 * Real.exp 1 / L) ^ n := by
        rw [show 4 * Real.exp 1 / L = 4 / L * Real.exp 1 by ring, mul_pow, ← Real.exp_nat_mul, mul_one]

/- English proof (translation)
Introduce `α β n hαβ hn`. Establish `hd : 0 < β - α` using `by linarith`. Establish `ha : (2 / (β - α)) ≠ 0` using `by positivity`. Introduce `W`. Establish `hqe : (C (2 / (β - α)) * X - C ((α + β) / (β - α)) : ℝ[X]) = C (2 / (β - α)) * X + C (-((α + β) / (β - α)))`.

Rewrite using `[C_neg, sub_eq_add_neg]`. Establish `hq : (C (2 / (β - α)) * X - C ((α + β) / (β - α)) : ℝ[X]).natDegree = 1`. Rewrite using `[hqe]`. Conclude with `natDegree_linear ha`. Establish `hl : (C (2 / (β - α)) * X - C ((α + β) / (β - α)) : ℝ[X]).leadingCoeff = 2 / (β - α)`.

Rewrite using `[hqe]`. Conclude with `leadingCoeff_linear ha`. Establish `hdeg : W.natDegree = n`. Simplify using `only [W, natDegree_comp, hq, Chebyshev.natDegree_T, Int.natAbs_natCast, mul_one]`. Establish `hev : ∀ Y : ℝ, W.eval Y = (Chebyshev.T ℝ n).eval ((2 * Y - α - β) / (β - α))`.

Introduce `Y`. Simplify using `only [W, eval_comp, eval_sub, eval_mul, eval_C, eval_X]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Use `⟨hdeg, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `: W.coeff n = W.leadingCoeff` using `by rw [leadingCoeff, hdeg]`. Rewrite using `[this]`. Simplify using `only [W]`. Rewrite using `[leadingCoeff_comp (by rw [hq]; exact one_ne_zero), hl, Chebyshev.leadingCoeff_T, Chebyshev.natDegree_T, Int.natAbs_natCast]`.

Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by omega⟩`. Rewrite using `[Nat.add_sub_cancel, show (4:ℝ) / (β - α) = 2 * (2 / (β - α)) by ring, mul_pow, pow_succ (2:ℝ) m]`. Expand and normalize the polynomial expressions, which then agree. Introduce `j`. Rewrite using `[hev, chebPt_eq]`.

Establish `: (2 * ((α + β) / 2 + (β - α) / 2 * Chebyshev.node n j) - α - β) / (β - α) = Chebyshev.node n j` using `by field_simp; ring`. Rewrite using `[this]`. Conclude with `Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt))`. Introduce `Y hY`. Rewrite using `[hev]`.

Apply `Chebyshev.abs_eval_T_real_le_one` to reduce the goal to its premises. Rewrite using `[abs_le]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[le_div_iff₀ hd]`. Combine the linear relations using `[hY.1]`.

Rewrite using `[div_le_iff₀ hd]`. Combine the linear relations using `[hY.2]`.
-/
theorem attained : Formalism.FourierDecayAlt.F7.ChebAttained := by
  intro α β n hαβ hn
  have hd : 0 < β - α := by linarith
  have ha : (2 / (β - α)) ≠ 0 := by positivity
  intro W
  have hqe : (C (2 / (β - α)) * X - C ((α + β) / (β - α)) : ℝ[X]) =
      C (2 / (β - α)) * X + C (-((α + β) / (β - α))) := by
    rw [C_neg, sub_eq_add_neg]
  have hq : (C (2 / (β - α)) * X - C ((α + β) / (β - α)) : ℝ[X]).natDegree = 1 := by
    rw [hqe]; exact natDegree_linear ha
  have hl : (C (2 / (β - α)) * X - C ((α + β) / (β - α)) : ℝ[X]).leadingCoeff = 2 / (β - α) := by
    rw [hqe]; exact leadingCoeff_linear ha
  have hdeg : W.natDegree = n := by
    simp only [W, natDegree_comp, hq, Chebyshev.natDegree_T, Int.natAbs_natCast, mul_one]
  have hev : ∀ Y : ℝ, W.eval Y = (Chebyshev.T ℝ n).eval ((2 * Y - α - β) / (β - α)) := by
    intro Y
    simp only [W, eval_comp, eval_sub, eval_mul, eval_C, eval_X]
    congr 1; field_simp; ring
  refine ⟨hdeg, ?_, ?_, ?_⟩
  · have : W.coeff n = W.leadingCoeff := by rw [leadingCoeff, hdeg]
    rw [this]
    simp only [W]
    rw [leadingCoeff_comp (by rw [hq]; exact one_ne_zero), hl, Chebyshev.leadingCoeff_T,
      Chebyshev.natDegree_T, Int.natAbs_natCast]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel, show (4:ℝ) / (β - α) = 2 * (2 / (β - α)) by ring, mul_pow, pow_succ (2:ℝ) m]
    ring
  · intro j
    rw [hev, chebPt_eq]
    have : (2 * ((α + β) / 2 + (β - α) / 2 * Chebyshev.node n j) - α - β) / (β - α)
        = Chebyshev.node n j := by field_simp; ring
    rw [this]
    exact Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp j.isLt))
  · intro Y hY
    rw [hev]
    apply Chebyshev.abs_eval_T_real_le_one
    rw [abs_le]
    constructor
    · rw [le_div_iff₀ hd]; linarith [hY.1]
    · rw [div_le_iff₀ hd]; linarith [hY.2]

end Formalism.FourierDecayAlt.P.ChebyshevExtremalPolynomials

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
The claim follows from `ChebyshevExtremalPolynomials.sharp`.
-/
theorem chebyshev_bound_sharp : Formalism.FourierDecayAlt.F7.ChebSharp := ChebyshevExtremalPolynomials.sharp

/- English proof (translation)
The claim follows from `ChebyshevExtremalPolynomials.coValue`.
-/
theorem chebyshev_coeff_value : Formalism.FourierDecayAlt.F7.ChebCoValue := ChebyshevExtremalPolynomials.coValue

/- English proof (translation)
The claim follows from `ChebyshevExtremalPolynomials.attained`.
-/
theorem chebyshev_bound_attained : Formalism.FourierDecayAlt.F7.ChebAttained := ChebyshevExtremalPolynomials.attained

/- English proof (translation)
The claim follows from `ChebyshevExtremalPolynomials.leadBound`.
-/
theorem chebyshev_leading_coeff_bound : Formalism.FourierDecayAlt.F7.ChebLeadBound := ChebyshevExtremalPolynomials.leadBound

/- English proof (translation)
The claim follows from `ChebyshevExtremalPolynomials.spacing`.
-/
theorem chebyshevNodeSpacing_true : Formalism.FourierDecayAlt.F7.ChebSpacing := ChebyshevExtremalPolynomials.spacing

/- English proof (translation)
The claim follows from `ChebyshevExtremalPolynomials.equiCo`.
-/
theorem equioscillation_coeff : Formalism.FourierDecayAlt.F7.EquiCo := ChebyshevExtremalPolynomials.equiCo

/- English proof (translation)
The claim follows from `ChebyshevExtremalPolynomials.equiCoBound`.
-/
theorem equioscillation_coeff_bound : Formalism.FourierDecayAlt.F7.EquiCoBound := ChebyshevExtremalPolynomials.equiCoBound

end Formalism.FourierDecayAlt.P
