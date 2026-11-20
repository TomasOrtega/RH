import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.BiadditiveInSingleVariables

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds

namespace GlobalTheory

namespace RadiiIdentities

/- English proof (translation)
Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sub_one_pos {l : ℕ} (hl : 2 ≤ l) : (0 : ℝ) < (l : ℝ) - 1 := by
  have : (2 : ℝ) ≤ l := by exact_mod_cast hl
  linarith

/- English proof (translation)
Expand and normalize the polynomial expressions, which then agree.
-/
theorem sq_sub_one_eq (l : ℕ) : (l : ℝ) ^ 2 - 1 = ((l : ℝ) - 1) * ((l : ℝ) + 1) := by
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Check the signs of the components of the expression. Prove the components needed by the constructor for the conclusion. Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exponent_integral : Formalism.L2.FormalSeriesBounds.EInt := by
  intro l i hl hi
  have h1 : (0 : ℝ) < (l : ℝ) - 1 := sub_one_pos hl
  have hsq : ((l : ℝ) ^ 2 - 1) ≠ 0 := by
    rw [sq_sub_one_eq]
    have : (0 : ℝ) < (l : ℝ) + 1 := by linarith
    positivity
  constructor
  · simp only [gam, rho]
    field_simp
  · obtain ⟨k, rfl⟩ := hi
    have hk : (2 * k + 1 - 1) / 2 = k := by omega
    have hne : ((l : ℝ) ^ 2) ≠ 1 := by
      intro h
      apply hsq
      rw [h]
      ring
    simp only [expE, hk, Ereal, rho]
    push_cast
    rw [geom_sum_eq hne]
    field_simp
    ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem radii_sum : I1 := by
  intro l i hl
  have h1 : (0 : ℝ) < (l : ℝ) - 1 := sub_one_pos hl
  have h2 : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hpow : ((l : ℝ) ^ i) ≠ 0 := by positivity
  refine ⟨?_, ?_⟩
  · simp only [r1, r2]
    field_simp
    ring
  · simp only [Ereal, rho]
    rw [sq_sub_one_eq]
    field_simp
    ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem slope_identity : I2 := by
  intro l i hl hi
  have h1 : (0 : ℝ) < (l : ℝ) - 1 := sub_one_pos hl
  have h2 : (0 : ℝ) < (l : ℝ) + 1 := by linarith
  have hsq : ((l : ℝ) ^ 2 - 1) = ((l : ℝ) - 1) * ((l : ℝ) + 1) := sq_sub_one_eq l
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl
  have hli : (l : ℝ) ≤ (l : ℝ) ^ i := by
    calc (l : ℝ) = (l : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (l : ℝ) ^ i := pow_le_pow_right₀ (by linarith) hi
  refine ⟨?_, ?_⟩
  · simp only [Ereal, rho, gam]
    rw [hsq]
    field_simp
    ring
  · simp only [gam]
    rw [hsq, sub_nonneg, mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Move the embeddings inside the algebraic operations. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem val_natCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℕ) :
    0 ≤ v (n : C) := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    calc (0 : WithTop ℝ) ≤ min (v (k : C)) (v 1) := by
          rw [AddValuation.map_one]
          exact le_min ih le_rfl
      _ ≤ v ((k : C) + 1) := AddValuation.map_add v _ _

/- English proof (translation)
Separate the alternatives or extract the components of the hypothesis. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem val_intCast_nonneg {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (n : ℤ) :
    0 ≤ v (n : C) := by
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · exact_mod_cast val_natCast_nonneg v k
  · push_cast
    rw [AddValuation.map_neg]
    exact val_natCast_nonneg v k

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Move the embeddings inside the algebraic operations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem val_other_prime : ValOther := by
  intro C _ v l hl hvl p hp hpl
  refine le_antisymm ?_ (val_natCast_nonneg v p)
  by_contra hlt
  rw [not_le] at hlt
  have hcop : Nat.Coprime l p := (Nat.coprime_primes hl hp).2 (Ne.symm hpl)
  have hbez : ((1 : ℤ) : C) = ((l : ℤ) * Nat.gcdA l p + (p : ℤ) * Nat.gcdB l p : ℤ) := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
    simp
  push_cast at hbez
  have hA : (0 : WithTop ℝ) < v ((l : C) * (Nat.gcdA l p : C)) := by
    rw [AddValuation.map_mul, hvl]
    exact lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1))
      (le_add_of_nonneg_right (val_intCast_nonneg v _))
  have hB : (0 : WithTop ℝ) < v ((p : C) * (Nat.gcdB l p : C)) := by
    rw [AddValuation.map_mul]
    exact lt_of_lt_of_le hlt (le_add_of_nonneg_right (val_intCast_nonneg v _))
  have hsum := AddValuation.map_add v ((l : C) * (Nat.gcdA l p : C)) ((p : C) * (Nat.gcdB l p : C))
  rw [← hbez, AddValuation.map_one] at hsum
  exact absurd (lt_of_lt_of_le (lt_min hA hB) hsum) (lt_irrefl 0)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.
-/
theorem weight_forms_agree : WeightConditionIff := by
  intro C _ v l i n0 h1
  have e1 : rho l + 1 / (2 * (l : ℝ) ^ i) - 1 / (8 * (l : ℝ) ^ i) =
      rho l + ((l : ℝ) ^ i)⁻¹ / 2 - ((l : ℝ) ^ i)⁻¹ / 8 := by ring
  have e2 : rho l + 1 / 2 - 1 / (8 * (l : ℝ) ^ i) = rho l + 1 / 2 - ((l : ℝ) ^ i)⁻¹ / 8 := by ring
  simp only [HM1, WeightCond, r1, r2, del, e1, e2]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Split into cases according to the possible forms of the given data. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem binomial_differences : F5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y s
    have hf : (s.factorial : ℚ) ≠ 0 := by exact_mod_cast s.factorial_ne_zero
    have key : (s.factorial : ℤ) * Ring.choose y s = ∏ j ∈ Finset.range s, (y - (j : ℤ)) := by
      rw [← descPochhammer_eval_eq_prod_range, Polynomial.eval_eq_smeval,
        Ring.descPochhammer_eq_factorial_smul_choose, nsmul_eq_mul]
    rw [eq_div_iff hf, mul_comm]
    exact_mod_cast key
  · intro y s
    rw [Ring.choose_succ_succ]
    ring
  · intro y
    simp
  · intro s
    cases s with
    | zero => simp
    | succ k => simp [Ring.choose_zero_succ]

end RadiiIdentities

open RadiiIdentities in

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem radii_valuation_differences :
    Formalism.L2.FormalSeriesBounds.EInt ∧ I1 ∧ I2 ∧ ValOther ∧ WeightConditionIff ∧ F5 :=
  ⟨exponent_integral, radii_sum, slope_identity, val_other_prime, weight_forms_agree,
    binomial_differences⟩

end GlobalTheory
