import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OrdLeTotientQS

open Formalism.BasicNotions

/- English proof (translation)
Introduce `R H`. Establish `hQS : H.QS ≤ R.n ^ 2` using `H.QS_le`. Establish `h2 : 2 * R.ord ≤ H.QS` using `(UpperTheory.Ram.ord_le_totient_QS H.toHostAx).2`. Establish `hf : (R.f : ℝ) = 2 * (R.n : ℝ)`. Simplify using `only [Ranks.f]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hn : (R.n : ℝ) = (R.ord : ℝ)` using `by simp [Ranks.n]`. Establish `hq1 : (1 : ℝ) ≤ H.q`. Use `H.qd_big.1` as an intermediate fact.

Conclude with `(by omega : 1 ≤ H.q)` after adjusting the coercions. Establish `hd1 : (1 : ℝ) ≤ H.d`. Use `H.qd_big.2` as an intermediate fact. Conclude with `(by omega : 1 ≤ H.d)` after adjusting the coercions. Establish `hQSr : (H.QS : ℝ) ≤ (R.n : ℝ) ^ 2` using `by exact_mod_cast hQS`.

Establish `h2r : 2 * (R.n : ℝ) ≤ H.QS`. Rewrite using `[hn]`. Conclude with `h2` after adjusting the coercions. Establish `hn0 : (0 : ℝ) ≤ R.n` using `Nat.cast_nonneg _`. Establish `hqd : (0 : ℝ) ≤ (H.q : ℝ) * H.d` using `by positivity`.

Establish `hqd1 : (1 : ℝ) ≤ (H.q : ℝ) * H.d` using `by nlinarith`. Rewrite using `[hf]`. Use `⟨?_, ?_, h2r⟩` and prove the remaining obligations. Establish `: (H.QS : ℝ) ≤ 4 * (2 * (R.n : ℝ) / 2) ^ 2` using `by nlinarith`. Use `mul_le_mul_of_nonneg_right this hqd` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Establish `hsq : 4 * (2 * (R.n : ℝ) / 2) ^ 2 ≤ (H.QS : ℝ) ^ 2` using `by nlinarith`. Establish `hqq : (H.q : ℝ) * H.d ≤ ((H.q : ℝ) * H.d) ^ 2` using `by nlinarith`. Establish `hA : (0 : ℝ) ≤ 4 * (2 * (R.n : ℝ) / 2) ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
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
