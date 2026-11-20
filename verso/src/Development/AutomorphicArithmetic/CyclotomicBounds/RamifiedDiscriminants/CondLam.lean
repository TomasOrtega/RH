import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OrdLeTotientQS

open Formalism.BasicNotions

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem UpperTheory.Ram.cond_le_four_n_sq :
    ∀ (R : Ranks) (H : Host R), (H.QS : ℝ) * H.q * H.d ≤ 4 * ((R.f : ℝ) / 2) ^ 2 * H.q * H.d ∧ 4 * ((R.f : ℝ) / 2) ^ 2 * H.q * H.d ≤ ((H.QS : ℝ) * H.q * H.d) ^ 2 ∧ (R.f : ℝ) ≤ H.QS := by
  intro R H
  have hQS : H.QS ≤ R.n ^ 2 := H.QS_le
  have h2 : 2 * R.ord ≤ H.QS := (UpperTheory.Ram.ord_le_totient_QS H.toHostAx).2
  have hf : (R.f : ℝ) = 2 * (R.n : ℝ) := by
    simp only [Ranks.f]
    push_cast
    ring
  have hn : (R.n : ℝ) = (R.ord : ℝ) := by simp [Ranks.n]
  have hq1 : (1 : ℝ) ≤ H.q := by
    have := H.qd_big.1
    exact_mod_cast (by omega : 1 ≤ H.q)
  have hd1 : (1 : ℝ) ≤ H.d := by
    have := H.qd_big.2
    exact_mod_cast (by omega : 1 ≤ H.d)
  have hQSr : (H.QS : ℝ) ≤ (R.n : ℝ) ^ 2 := by exact_mod_cast hQS
  have h2r : 2 * (R.n : ℝ) ≤ H.QS := by
    rw [hn]; exact_mod_cast h2
  have hn0 : (0 : ℝ) ≤ R.n := Nat.cast_nonneg _
  have hqd : (0 : ℝ) ≤ (H.q : ℝ) * H.d := by positivity
  have hqd1 : (1 : ℝ) ≤ (H.q : ℝ) * H.d := by nlinarith
  rw [hf]
  refine ⟨?_, ?_, h2r⟩
  · have : (H.QS : ℝ) ≤ 4 * (2 * (R.n : ℝ) / 2) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right this hqd
    nlinarith
  · have hsq : 4 * (2 * (R.n : ℝ) / 2) ^ 2 ≤ (H.QS : ℝ) ^ 2 := by nlinarith
    have hqq : (H.q : ℝ) * H.d ≤ ((H.q : ℝ) * H.d) ^ 2 := by nlinarith
    have hA : (0 : ℝ) ≤ 4 * (2 * (R.n : ℝ) / 2) ^ 2 := by positivity
    calc 4 * (2 * (R.n : ℝ) / 2) ^ 2 * H.q * H.d = 4 * (2 * (R.n : ℝ) / 2) ^ 2 * ((H.q : ℝ) * H.d) := by ring
      _ ≤ (H.QS : ℝ) ^ 2 * ((H.q : ℝ) * H.d) ^ 2 := mul_le_mul hsq hqq hqd (by positivity)
      _ = ((H.QS : ℝ) * H.q * H.d) ^ 2 := by ring
