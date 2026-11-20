import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLogDivSubOneLeThreeMulLogAddOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NewPrimesSetDescription
import Development.AutomorphicArithmetic.PrimeDiscriminants.BadCount
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestClassSelfIntersectionStatement

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

/- English proof (translation)
Establish `hpr` using `(GlobalTheory.Mean4.setB_newP_facts D Y B₀ B₀ (by linarith)).2.1`. Establish `hfl : 48 ≤ ⌊B₀⌋₊` using `Nat.le_floor (by exact_mod_cast hB)`. Establish `hM` using `D.host.sum_log_div_le_of_bad ⌊B₀⌋₊ Y.lev (setB Y B₀) (by omega) (by unfold FewBad at hF; omega) hpr fun p h1 h2 => by`. Rewrite `h1` using `[setB, Finset.mem_union]`. Break down `h1 with h | h` into its components or cases.

Rewrite `h` using `[Finset.mem_filter, Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `h0` using `D.host.log_rdE_nonneg'`. Establish `h48 : 4 * Real.log D.host.rdE / (⌊B₀⌋₊ : ℝ) ≤ 4 * Real.log D.host.rdE / 48` using `div_le_div_of_nonneg_left (by linarith) (by norm_num) (by exact_mod_cast hfl)`.

Establish `hlog : Real.log (⌊B₀⌋₊ : ℝ) ≤ Real.log B₀` using `Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊B₀⌋₊)) (Nat.floor_le (by linarith))`. Establish `hle : ∑ p ∈ setB Y B₀, (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) ≤ ∑ p ∈ setB Y B₀, Real.log p / ((p : ℝ) - 1)`. Use `Finset.sum_le_sum fun p hp => ?_` and prove the remaining obligations. Establish `h2 : (2 : ℝ) ≤ p` using `by exact_mod_cast (hpr p hp).two_le`. Establish `hl : 0 ≤ Real.log p` using `Real.log_nonneg (by linarith)`.

Rewrite using `[div_le_div_iff₀ (by nlinarith) (by linarith)]`. Establish `: 0 ≤ Real.log p * ((p : ℝ) - 1)` using `mul_nonneg hl (by linarith)`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_setB_le_log (D : D7) (Y : ShimX D.what₂.Tau) (B₀ : ℝ) (hB : 48 ≤ B₀) (hF : FewBad Y) :
    ∑ p ∈ setB Y B₀, (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) ≤ 3 * Real.log B₀ + 1 + Real.log D.host.rdE / 12 := by
  have hpr := (GlobalTheory.Mean4.setB_newP_facts D Y B₀ B₀ (by linarith)).2.1
  have hfl : 48 ≤ ⌊B₀⌋₊ := Nat.le_floor (by exact_mod_cast hB)
  have hM := D.host.sum_log_div_le_of_bad ⌊B₀⌋₊ Y.lev (setB Y B₀) (by omega) (by unfold FewBad at hF; omega) hpr
    fun p h1 h2 => by
      rw [setB, Finset.mem_union] at h1
      rcases h1 with h | h
      · rw [Finset.mem_filter, Finset.mem_range] at h
        omega
      · exact h
  have h0 := D.host.log_rdE_nonneg'
  have h48 : 4 * Real.log D.host.rdE / (⌊B₀⌋₊ : ℝ) ≤ 4 * Real.log D.host.rdE / 48 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) (by exact_mod_cast hfl)
  have hlog : Real.log (⌊B₀⌋₊ : ℝ) ≤ Real.log B₀ :=
    Real.log_le_log (by exact_mod_cast (by omega : 0 < ⌊B₀⌋₊)) (Nat.floor_le (by linarith))
  have hle : ∑ p ∈ setB Y B₀, (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1) ≤
      ∑ p ∈ setB Y B₀, Real.log p / ((p : ℝ) - 1) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hpr p hp).two_le
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
    have : 0 ≤ Real.log p * ((p : ℝ) - 1) := mul_nonneg hl (by linarith)
    nlinarith
  linarith

/- English proof (translation)
Introduce `r`. Use `⟨|r| + 5, by positivity, ?_⟩` and prove the remaining obligations. Introduce `D Y Φ hh B₀ a b hB hV hP hF hT hE`. Take `⟨hc, hcomb, hI, hsh, htot, hrest⟩` from `GlobalTheory.T.test_class_self_intersection D Y hP`. Establish `hlim` using `hE _ hc`.

Rewrite `hlim` using `[hcomb, hsh, htot, hT B₀ (by linarith)]`. Establish `hneg : 2 * testI Y * Y.vol < 0` using `by nlinarith`. Establish `hle` using `le_of_tendsto' hlim (b := 0) (fun n => by`. Use `Finset.sum_nonpos fun p hp => ?_` and prove the remaining obligations. Establish `hp'` using `((GlobalTheory.Mean4.setB_newP_facts D Y B₀ n (by linarith)).2.2.1 p).1 hp`.

Establish `h2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp'.1.two_le`. Rewrite using `[hrest p hp'.1.two_le]`. Conclude with `mul_nonpos_of_nonpos_of_nonneg hneg.le (div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)))`. Establish `hS` using `sum_setB_le_log D Y B₀ hB hF`. Use `set S := ∑ p ∈ setB Y B₀, (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1)`.

Establish `key : 0 ≤ a - (r - 1 / 2 - S)`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_le]`. Use `mul_pos_of_neg_of_neg hneg h` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `h1 : 1 ≤ Real.log B₀`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : -r ≤ |r|` using `neg_le_abs r`.

Establish `h3 : |r| ≤ |r| * Real.log B₀` using `le_mul_of_one_le_right (abs_nonneg r) h1`. Establish `h4` using `mul_nonneg (abs_nonneg r) D.host.log_rdE_nonneg'`. Establish `h5` using `D.host.log_rdE_nonneg'`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem neg_first_coeff_le_log : ∀ r : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (Y : ShimX D.what₂.Tau), ∀ (Φ : ℝ → Fn Y) (hh : Fn Y), ∀ B₀ a b : ℝ, 48 ≤ B₀ → 0 < Y.vol → Propor Y → FewBad Y → TestVal Φ hh r → ExactAt Φ hh B₀ a b → -a ≤ C * (Real.log B₀ + Real.log D.host.rdE) := by
  intro r
  refine ⟨|r| + 5, by positivity, ?_⟩
  intro D Y Φ hh B₀ a b hB hV hP hF hT hE
  obtain ⟨hc, hcomb, hI, hsh, htot, hrest⟩ := GlobalTheory.T.test_class_self_intersection D Y hP
  have hlim := hE _ hc
  rw [hcomb, hsh, htot, hT B₀ (by linarith)] at hlim
  have hneg : 2 * testI Y * Y.vol < 0 := by nlinarith
  have hle := le_of_tendsto' hlim (b := 0) (fun n => by
    refine Finset.sum_nonpos fun p hp => ?_
    have hp' := ((GlobalTheory.Mean4.setB_newP_facts D Y B₀ n (by linarith)).2.2.1 p).1 hp
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp'.1.two_le
    rw [hrest p hp'.1.two_le]
    exact mul_nonpos_of_nonpos_of_nonneg hneg.le
      (div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)))
  have hS := sum_setB_le_log D Y B₀ hB hF
  set S := ∑ p ∈ setB Y B₀, (p : ℝ) * Real.log p / ((p : ℝ) ^ 2 - 1)
  have key : 0 ≤ a - (r - 1 / 2 - S) := by
    by_contra h
    rw [not_le] at h
    have := mul_pos_of_neg_of_neg hneg h
    nlinarith
  have h1 : 1 ≤ Real.log B₀ := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have h2 : -r ≤ |r| := neg_le_abs r
  have h3 : |r| ≤ |r| * Real.log B₀ := le_mul_of_one_le_right (abs_nonneg r) h1
  have h4 := mul_nonneg (abs_nonneg r) D.host.log_rdE_nonneg'
  have h5 := D.host.log_rdE_nonneg'
  nlinarith

end GlobalTheory.Mean4
