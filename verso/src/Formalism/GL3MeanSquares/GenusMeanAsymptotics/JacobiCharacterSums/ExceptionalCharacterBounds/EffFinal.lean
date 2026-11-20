import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffPsi
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffConsts
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffExc
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.PsiAPLeCount
import Mathlib

open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Separate the alternatives or extract the components of the hypothesis. Rewrite the conclusion using the stated equalities.

Check the signs of the components of the expression. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
theorem progSupplyOf (A : ℕ) (hA : ExcBoundAt A) : ∃ K : ℝ, 4 ≤ K ∧ ∀ (m a : ℕ) (x : ℝ), 1 ≤ m → Nat.Coprime a m →
    K * Real.log (3 * m) ^ 2 ≤ Real.log x → Real.sqrt x ≤ ((primesAP m a x).card : ℝ) := by
  obtain ⟨c, c₀, C, hc, hc₀, hC, hlow⟩ := psiAPLowerOf A hA
  obtain ⟨K, hK, hsz⟩ := constsOf A c c₀ C hc hc₀ hC
  refine ⟨K, hK, fun m a x hm ha hx => ?_⟩
  rcases le_or_gt x 0 with hx0 | hx0
  · rw [Real.sqrt_eq_zero'.mpr hx0]; positivity
  obtain ⟨h4, hrange, hmain⟩ := hsz m x hm hx0 hx
  have hψ := hlow m a x hm ha hx0 h4 hrange
  have hx1 : 1 ≤ x := by
    by_contra h
    push Not at h
    have := Real.log_nonpos hx0.le h.le
    linarith
  have hcnt := psiAP_le_count m a x hx1
  have hLpos : 0 < Real.log x := by linarith
  have h2 : Real.log x * Real.sqrt x ≤ Real.log x * ((primesAP m a x).card : ℝ) := by
    nlinarith
  exact le_of_mul_le_mul_left h2 hLpos

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Put the polynomial expressions in normal form. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation. Reduce the claim to the hypotheses of an applicable result. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem supplyPrimesOf (A : ℕ) (hA : ExcBoundAt A) : ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, 1 ≤ m → ∃ S : Finset ℕ, S.card = n ∧
    ∀ q ∈ S, q.Prime ∧ q ≡ 1 [MOD m] ∧ (q : ℝ) ≤ Real.exp (C * Real.log (2 * m * (n + 2)) ^ 2) := by
  obtain ⟨K, hK, hP⟩ := progSupplyOf A hA
  refine ⟨K, by linarith, fun m n hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set ℓ := Real.log (2 * (m : ℝ) * ((n : ℝ) + 2)) with hℓdef
  set x := Real.exp (K * ℓ ^ 2) with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have h30 : 0 ≤ Real.log (3 * (m : ℝ)) := Real.log_nonneg (by linarith)
  have h3 : Real.log (3 * (m : ℝ)) ≤ ℓ := Real.log_le_log (by positivity) (by nlinarith)
  have hcond : K * Real.log (3 * (m : ℝ)) ^ 2 ≤ Real.log x := by
    rw [hxdef, Real.log_exp]
    have := pow_le_pow_left₀ h30 h3 2
    nlinarith
  have hcard := hP m 1 x hm (Nat.coprime_one_left m) hcond
  have hℓ1 : Real.log ((n : ℝ) + 2) ≤ ℓ := Real.log_le_log (by positivity) (by nlinarith)
  have hℓ4 : Real.log 4 ≤ ℓ := Real.log_le_log (by norm_num) (by nlinarith)
  have hlog4 : (1 : ℝ) ≤ Real.log 4 := by
    have h2 : Real.exp 1 ≤ 4 := by
      have := Real.exp_one_lt_d9; linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log 4 := Real.log_le_log (Real.exp_pos 1) h2
  have hsq : Real.sqrt x = Real.exp (K * ℓ ^ 2 / 2) := by
    have he : Real.exp (K * ℓ ^ 2) = Real.exp (K * ℓ ^ 2 / 2) * Real.exp (K * ℓ ^ 2 / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [hxdef, he, Real.sqrt_mul_self (Real.exp_pos _).le]
  have hnx : (n : ℝ) ≤ Real.sqrt x := by
    rw [hsq]
    calc (n : ℝ) ≤ (n : ℝ) + 2 := by linarith
      _ = Real.exp (Real.log ((n : ℝ) + 2)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (K * ℓ ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  have hn : n ≤ (primesAP m 1 x).card := by exact_mod_cast hnx.trans hcard
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hn
  refine ⟨S, hScard, fun q hq => ?_⟩
  have hmem := hSsub hq
  simp only [primesAP, Finset.mem_filter, Finset.mem_Icc] at hmem
  obtain ⟨⟨_, hqx⟩, hqp, hqm⟩ := hmem
  refine ⟨hqp, hqm, ?_⟩
  exact (Nat.cast_le.mpr hqx).trans (Nat.floor_le hx0.le)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem supplyPrimesEff : ∃ C : ℝ, 0 < C ∧ ∀ m n : ℕ, 1 ≤ m → ∃ S : Finset ℕ, S.card = n ∧
    ∀ q ∈ S, q.Prime ∧ q ≡ 1 [MOD m] ∧ (q : ℝ) ≤ Real.exp (C * Real.log (2 * m * (n + 2)) ^ 2) :=
  supplyPrimesOf 2 excBoundEff

end Formalism.HermitianLattices.Ext.SupplyAP
