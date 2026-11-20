import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizePos

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec

namespace GlobalTheory.Dec.BoundedDistance

/- English proof (translation)
Establish `hf' : (f : ℝ) ≠ 0` using `by exact_mod_cast hf.ne'`. Establish `he : 1 ≤ Real.exp (R / f)` using `Real.one_le_exp (div_nonneg hR (Nat.cast_nonneg _))`. Establish `hone : 1 ≤ s * Real.exp (R / f) / la`. Rewrite using `[le_div_iff₀ hla]`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hbase0 : 0 ≤ 1 + 2 * s * Real.exp (R / f) / la` using `by positivity`. Establish `hbase : 1 + 2 * s * Real.exp (R / f) / la ≤ 3 * s / la * Real.exp (R / f)`. Establish `h3 : 3 * s / la * Real.exp (R / f) = s * Real.exp (R / f) / la + 2 * s * Real.exp (R / f) / la` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hk : 2 * (m * f) = 2 * m * f` using `by ring`.

Rewrite using `[hk]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_pow, ← Real.exp_nat_mul]`. Use `congr 2`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem bound_le (s la R : ℝ) (m f : ℕ) (hs : 1 ≤ s) (hla : 0 < la) (hla1 : la ≤ 1) (hR : 0 ≤ R) (hf : 0 < f) :
    (1 + 2 * s * Real.exp (R / f) / la) ^ (2 * (m * f)) ≤ (3 * s / la) ^ (2 * m * f) * Real.exp (2 * (m : ℝ) * R) := by
  have hf' : (f : ℝ) ≠ 0 := by exact_mod_cast hf.ne'
  have he : 1 ≤ Real.exp (R / f) := Real.one_le_exp (div_nonneg hR (Nat.cast_nonneg _))

  have hone : 1 ≤ s * Real.exp (R / f) / la := by
    rw [le_div_iff₀ hla]
    nlinarith
  have hbase0 : 0 ≤ 1 + 2 * s * Real.exp (R / f) / la := by positivity
  have hbase : 1 + 2 * s * Real.exp (R / f) / la ≤ 3 * s / la * Real.exp (R / f) := by
    have h3 : 3 * s / la * Real.exp (R / f) =
        s * Real.exp (R / f) / la + 2 * s * Real.exp (R / f) / la := by ring
    linarith
  have hk : 2 * (m * f) = 2 * m * f := by ring
  rw [hk]
  calc (1 + 2 * s * Real.exp (R / f) / la) ^ (2 * m * f)
      ≤ (3 * s / la * Real.exp (R / f)) ^ (2 * m * f) := pow_le_pow_left₀ hbase0 hbase _
    _ = (3 * s / la) ^ (2 * m * f) * Real.exp (2 * (m : ℝ) * R) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      field_simp

/- English proof (translation)
Introduce `I x y r hn hr`. Take `⟨hfin, hcard⟩` from `GlobalTheory.RationalCount.count_le I x y r hn hr`. Establish `hx` using `GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn x`. Establish `hy` using `GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn y`. Establish `hx2 : tau1 I x ≤ 1 / 2` using `by unfold tau1; exact min_le_left _ _`.

Establish `hy2 : tau1 I y ≤ 1 / 2` using `by unfold tau1; exact min_le_left _ _`. Establish `hs : (1 : ℝ) ≤ Real.sqrt I.n`. Rewrite using `[show (1 : ℝ) = Real.sqrt 1 by simp]`. Conclude with `Real.sqrt_le_sqrt (by exact_mod_cast hn)`. Establish `hf : 0 < I.f` using `Module.finrank_pos`.

Establish `hla1 : tau1 I x * tau1 I y ≤ 1` using `by nlinarith`. Establish `key` using `bound_le (Real.sqrt I.n) (tau1 I x * tau1 I y) (∑ v, r v) (I.n ^ 2) I.f hs (mul_pos hx hy) hla1 (Finset.sum_nonneg fun v _ => hr v) hf`. Move the coercions through the operations in `at key`. Conclude with `⟨hfin, hcard.trans key⟩`.
-/
theorem countRat : CountRat := by
  intro I x y r hn hr
  obtain ⟨hfin, hcard⟩ := GlobalTheory.RationalCount.count_le I x y r hn hr
  have hx := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn x
  have hy := GlobalTheory.RationalCount.truncatedLeastLatticeSize_pos I hn y

  have hx2 : tau1 I x ≤ 1 / 2 := by unfold tau1; exact min_le_left _ _
  have hy2 : tau1 I y ≤ 1 / 2 := by unfold tau1; exact min_le_left _ _
  have hs : (1 : ℝ) ≤ Real.sqrt I.n := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  have hf : 0 < I.f := Module.finrank_pos
  have hla1 : tau1 I x * tau1 I y ≤ 1 := by nlinarith
  have key := bound_le (Real.sqrt I.n) (tau1 I x * tau1 I y) (∑ v, r v) (I.n ^ 2) I.f hs
    (mul_pos hx hy) hla1 (Finset.sum_nonneg fun v _ => hr v) hf
  push_cast at key
  exact ⟨hfin, hcard.trans key⟩

end GlobalTheory.Dec.BoundedDistance
