import Formalism.FrobeniusBaseCase.Statement

namespace Formalism.BaseCaseIdentities

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Replace the relevant objects with their definitions. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Replace the relevant objects with their definitions.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem id20_statement : Id20 := by
  intro l i hl
  have h2 : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hq : ((l:ℝ)^2 - 1) ≠ 0 := by nlinarith
  have h1 : ((l:ℝ) - 1) ≠ 0 := by linarith
  have hL : ((l:ℝ)^i) ≠ 0 := by positivity
  constructor
  · unfold gam rho; field_simp; ring
  · unfold r1 del sg; field_simp; ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Replace the relevant objects with their definitions. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem slopeSumIdentity_statement : SlopeSumIdentity := by
  intro l i hl
  have h2 : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hq : ((l:ℝ)^2 - 1) ≠ 0 := by nlinarith
  have h1 : ((l:ℝ) - 1) ≠ 0 := by linarith
  have hL : ((l:ℝ)^i) ≠ 0 := by positivity
  unfold Lnum r1 r2 Enum rho; field_simp; ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem geomSlopeIdentity_statement : GeomSlopeIdentity := by
  intro l i hl hi
  obtain ⟨t, rfl⟩ := hi
  have h2 : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hq : ((l:ℝ)^2 - 1) ≠ 0 := by nlinarith
  have hs : s0 (2 * t + 1) = t := by unfold s0; omega
  rw [hs]
  unfold qnum Enum rho; field_simp; ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sqMulIdentity_statement : SqMulIdentity := by
  intro l hl
  have h2 : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hq : ((l:ℝ)^2 - 1) ≠ 0 := by nlinarith
  unfold qnum rho; field_simp; ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem identity_twenty_d : PowMulThreeEighthsIdentity := by
  intro l i hl hi
  obtain ⟨t, rfl⟩ := hi
  have h2 : (2:ℝ) ≤ l := by exact_mod_cast hl
  have hl0 : (l:ℝ) ≠ 0 := by linarith
  have hs : Kn (2 * t + 1) = t + 1 := by unfold Kn; omega
  rw [hs]
  unfold qnum sg; field_simp; ring

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem eNum_eq_sum {l : ℕ} (hl : 2 ≤ l) (s : ℕ) :
    eNum l s = ∑ j ∈ Finset.range s, (l ^ 2) ^ j := by
  have : 2 ≤ l ^ 2 := by nlinarith
  unfold eNum; rw [Nat.geomSum_eq this]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem identity_e : IdE := by
  intro l s hl
  have hq : 2 ≤ l ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [eNum_eq_sum hl]; simp
  · rw [eNum_eq_sum hl, eNum_eq_sum hl, Finset.sum_range_succ', Finset.mul_sum]
    simp only [pow_succ, pow_zero]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  · rw [eNum_eq_sum hl]
    have := geom_sum_mul_add (l ^ 2 - 1) s
    rwa [Nat.sub_add_cancel (by omega)] at this

/- English proof (translation)
Establish an intermediate fact. Replace the relevant objects with their definitions. Establish an intermediate fact. Check the signs of the components of the expression.
-/
theorem rho_pos {l : ℕ} (hl : 3 ≤ l) : 0 < rho l := by
  have h2 : (3:ℝ) ≤ l := by exact_mod_cast hl
  unfold rho
  have : (0:ℝ) < (l:ℝ)^2 - 1 := by nlinarith
  positivity

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions. Clear the denominators using the available nonvanishing facts.
-/
theorem rho_mul {l : ℕ} (hl : 3 ≤ l) : ((l:ℝ)^2 - 1) * rho l = 1 := by
  have h2 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hq : ((l:ℝ)^2 - 1) ≠ 0 := by nlinarith
  unfold rho; field_simp

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Proceed by induction. Treat this case separately.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Use the polynomial consequences of the given equalities and inequalities. Move the embeddings inside the algebraic operations. Use the polynomial consequences of the given equalities and inequalities.

Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Use the polynomial consequences of the given equalities and inequalities.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem num_c {l : ℕ} (hl : 3 ≤ l) {j : ℕ} (hj : 3 ≤ j) :
    1 + rho l ≤ -((j:ℝ) - 1) + (l:ℝ)^j * rho l := by
  have h2 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hr := rho_pos hl
  have hm := rho_mul hl
  induction j, hj using Nat.le_induction with
  | base =>
    have h3 : 0 ≤ ((l:ℝ)^3 - 1 - 3 * ((l:ℝ)^2 - 1)) * rho l := by
      apply mul_nonneg _ hr.le
      nlinarith [mul_nonneg (sq_nonneg (l:ℝ)) (sub_nonneg.2 h2)]
    push_cast
    nlinarith
  | succ j hj ih =>
    have h4 : (l:ℝ)^2 ≤ (l:ℝ)^j := pow_le_pow_right₀ (by linarith) (by omega)
    have h5 : 0 ≤ ((l:ℝ)^j * ((l:ℝ) - 1) - ((l:ℝ)^2 - 1)) * rho l := by
      apply mul_nonneg _ hr.le
      nlinarith
    push_cast
    rw [pow_succ]
    nlinarith

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Proceed by induction. Treat this case separately. Use the polynomial consequences of the given equalities and inequalities.

Treat this case separately. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem num_d {l : ℕ} (hl : 3 ≤ l) {j : ℕ} (hj : 1 ≤ j) :
    1 + rho l ≤ -(j:ℝ) + (l:ℝ)^j * (1 + rho l) := by
  have h2 : (3:ℝ) ≤ l := by exact_mod_cast hl
  have hr := rho_pos hl
  induction j, hj using Nat.le_induction with
  | base => push_cast; nlinarith
  | succ j hj ih =>
    have h4 : (1:ℝ) ≤ (l:ℝ)^j := one_le_pow₀ (by linarith)
    have h5 : 1 ≤ (l:ℝ)^j * (((l:ℝ) - 1) * (1 + rho l)) := by
      have : 1 ≤ ((l:ℝ) - 1) * (1 + rho l) := by nlinarith
      nlinarith
    push_cast
    rw [pow_succ]
    nlinarith

/- English proof (translation)
Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem num_good {l : ℕ} (hl : 3 ≤ l) {j : ℕ} (hj : 2 ≤ j) :
    1 + rho l ≤ -((j:ℝ) - 1) + (l:ℝ)^j * (1 + rho l) := by
  have := num_d hl (j := j) (by omega)
  linarith

end Formalism.BaseCaseIdentities
