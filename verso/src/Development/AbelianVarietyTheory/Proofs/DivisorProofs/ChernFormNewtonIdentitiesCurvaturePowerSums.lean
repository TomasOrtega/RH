import Mathlib
import GroundTheory.GlobalFields.Artin.LogCharpoly
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

/- English proof (translation)
Break down `k with _ | k` into its components or cases. Simplify using the standard rewrite rules. Establish `h` using `congrArg (PowerSeries.coeff k) (GroundTheory.Global.coe_derivative_charpolyRev M)`. Rewrite `h` using `[Polynomial.coeff_coe, Polynomial.coeff_derivative, neg_mul, map_neg, mul_comm (M.charpolyRev : PowerSeries R), PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`. Simplify using `only [PowerSeries.coeff_mk, Polynomial.coeff_coe] at h`.

Rewrite using `[mul_comm]`. Simplify using `using h`.
-/
theorem newton_charpolyRev {R r : Type} [CommRing R] [Fintype r] [DecidableEq r] (M : Matrix r r R) (k : ℕ) :
    (k : R) * M.charpolyRev.coeff k =
      -∑ i ∈ Finset.range k, (M ^ (i + 1)).trace * M.charpolyRev.coeff (k - 1 - i) := by
  rcases k with _ | k
  · simp
  · have h := congrArg (PowerSeries.coeff k) (GroundTheory.Global.coe_derivative_charpolyRev M)
    rw [Polynomial.coeff_coe, Polynomial.coeff_derivative, neg_mul, map_neg, mul_comm (M.charpolyRev : PowerSeries R),
      PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
    simp only [PowerSeries.coeff_mk, Polynomial.coeff_coe] at h
    rw [mul_comm]
    simpa using h

/- English proof (translation)
Use `⟨?_, fun j => ?_⟩` and prove the remaining obligations. Establish `h : (Matrix.charpolyRev (-curvPoly G v)).coeff 0 = 1`. Rewrite using `[Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]`. Rewrite using `[chernAt, chernPoly, h, map_one, pow_zero, one_smul]`. Establish `h` using `congrArg (MvPolynomial.aeval (R := ℂ) (sym (n := n))) (newton_charpolyRev (-curvPoly G v) j)`.

Establish `hp (k : ℕ) : MvPolynomial.aeval (R` using `ℂ) (sym (n := n)) ((-curvPoly G v) ^ k).trace = (-1 : ℂ) ^ k • powAt G v k := by`. Establish `e : curvEv G v ^ k = (curvPoly G v ^ k).map (MvPolynomial.aeval (R` using `ℂ) (sym (n := n))) := (map_pow (MvPolynomial.aeval (R := ℂ) (sym (n := n))).mapMatrix (curvPoly G v) k).symm`. Rewrite using `[← neg_one_smul ℂ (curvPoly G v), smul_pow, Matrix.trace_smul, map_smul, powAt, e]`. Simplify using `only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]`. Rewrite `h` using `[map_mul, map_natCast, map_neg, map_sum]`.

Simplify using `only [map_mul, hp] at h`. Simplify using `only [chernAt, chernPoly]`. Rewrite using `[smul_comm, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, h, smul_neg, Finset.smul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations.

Establish `hi'` using `Finset.mem_range.1 hi`. Rewrite using `[mul_smul_comm, smul_mul_assoc, smul_smul, smul_smul]`. Use `congr 1`. Take `⟨m, rfl⟩ : ∃ m, j = i + 1 + m` from `⟨j - (i + 1), by omega⟩`. Rewrite using `[show i + 1 + m - 1 - i = m by omega, neg_pow kappa]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem chernAt_newton (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G : V n → Matrix r r ℂ) (v : V n) :
    chernAt G v 0 = 1 ∧ ∀ j : ℕ, (j : ℂ) • chernAt G v j =
      -∑ i ∈ Finset.range j, (-kappa) ^ (i + 1) • (powAt G v (i + 1) * chernAt G v (j - 1 - i)) := by
  refine ⟨?_, fun j => ?_⟩
  · have h : (Matrix.charpolyRev (-curvPoly G v)).coeff 0 = 1 := by
      rw [Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    rw [chernAt, chernPoly, h, map_one, pow_zero, one_smul]
  · have h := congrArg (MvPolynomial.aeval (R := ℂ) (sym (n := n))) (newton_charpolyRev (-curvPoly G v) j)
    have hp (k : ℕ) : MvPolynomial.aeval (R := ℂ) (sym (n := n)) ((-curvPoly G v) ^ k).trace =
        (-1 : ℂ) ^ k • powAt G v k := by
      have e : curvEv G v ^ k = (curvPoly G v ^ k).map (MvPolynomial.aeval (R := ℂ) (sym (n := n))) :=
        (map_pow (MvPolynomial.aeval (R := ℂ) (sym (n := n))).mapMatrix (curvPoly G v) k).symm
      rw [← neg_one_smul ℂ (curvPoly G v), smul_pow, Matrix.trace_smul, map_smul, powAt, e]
      simp only [Matrix.trace, Matrix.diag, map_sum, Matrix.map_apply]
    rw [map_mul, map_natCast, map_neg, map_sum] at h
    simp only [map_mul, hp] at h
    simp only [chernAt, chernPoly]
    rw [smul_comm, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, h, smul_neg, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [mul_smul_comm, smul_mul_assoc, smul_smul, smul_smul]
    congr 1
    obtain ⟨m, rfl⟩ : ∃ m, j = i + 1 + m := ⟨j - (i + 1), by omega⟩
    rw [show i + 1 + m - 1 - i = m by omega, neg_pow kappa]
    ring

end GlobalTheory.ChernCalc
