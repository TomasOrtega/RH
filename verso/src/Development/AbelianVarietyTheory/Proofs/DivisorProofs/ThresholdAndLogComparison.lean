import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMean
import Formalism.SharpRestriction.Divisibility.LatticeTransfer

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4

namespace GlobalTheory.Mean4

/- English proof (translation)
Break down `N with _ | m` into its components or cases. Simplify using `at h`. Simplify using `only [Nat.add_sub_cancel] at h`. Establish `h4 : 4 * m ≤ (m + 1) ^ 2` using `by nlinarith [sq_nonneg ((m : ℤ) - 1)]`. Use `Nat.mul_le_mul_left f h4` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem twelve_le_mul_sq (f N : ℕ) (h : 2 < f * (N - 1)) : 12 ≤ f * N ^ 2 := by
  rcases N with _ | m
  · simp at h
  · simp only [Nat.add_sub_cancel] at h
    have h4 : 4 * m ≤ (m + 1) ^ 2 := by nlinarith [sq_nonneg ((m : ℤ) - 1)]
    have := Nat.mul_le_mul_left f h4
    nlinarith

/- English proof (translation)
Introduce `D Y h`. Establish `hrd : 1 ≤ D.host.rdE`. Unfold `Formalism.BasicNotions.Host.rdE`. Apply `Real.one_le_rpow` to reduce the goal to its premises. Establish `h0` using `NumberField.discr_ne_zero D.host.E`.

Establish `h1 : (1 : ℤ) ≤ |NumberField.discr D.host.E|` using `Int.one_le_abs h0`. Conclude with `h1` after adjusting the coercions. Check the signs of the components of the expression. Use `⟨fun u g hw => ?_, hrd, fun B hB => ?_⟩` and prove the remaining obligations. Establish `h12 : (12 : ℝ) ≤ (D.R.f : ℝ) * (Y.N : ℝ) ^ 2` using `by exact_mod_cast twelve_le_mul_sq _ _ h`.

Establish `hs : 0 ≤ supAbs Y u` using `Real.iSup_nonneg fun _ => abs_nonneg _`. Establish `hq : 0 ≤ supAbs Y u / g` using `div_nonneg hs hw.1.le`. Unfold `bigB0`. Use the polynomial consequences of the given equalities and inequalities. Unfold `lg`.

Establish `h1 : Real.log B ≤ Real.log (B * D.host.rdE)` using `Real.log_le_log (by linarith) (by nlinarith)`. Combine the linear relations using `[abs_nonneg (dlogL D 1)]`.
-/
theorem threshold_ge_and_rootDiscr_ge : ∀ (D : D7) (Y : ShimX D.what₂.Tau), 2 < D.R.f * (Y.N - 1) → (∀ u g, WeightHyp Y u g → 48 ≤ bigB0 Y u g) ∧ 1 ≤ D.host.rdE ∧ ∀ B : ℝ, 1 ≤ B → Real.log B ≤ lg D B := by
  intro D Y h
  have hrd : 1 ≤ D.host.rdE := by
    unfold Formalism.BasicNotions.Host.rdE
    apply Real.one_le_rpow
    · have h0 := NumberField.discr_ne_zero D.host.E
      have h1 : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h0
      exact_mod_cast h1
    · positivity
  refine ⟨fun u g hw => ?_, hrd, fun B hB => ?_⟩
  · have h12 : (12 : ℝ) ≤ (D.R.f : ℝ) * (Y.N : ℝ) ^ 2 := by exact_mod_cast twelve_le_mul_sq _ _ h
    have hs : 0 ≤ supAbs Y u := Real.iSup_nonneg fun _ => abs_nonneg _
    have hq : 0 ≤ supAbs Y u / g := div_nonneg hs hw.1.le
    unfold bigB0
    nlinarith
  · unfold lg
    have h1 : Real.log B ≤ Real.log (B * D.host.rdE) :=
      Real.log_le_log (by linarith) (by nlinarith)
    linarith [abs_nonneg (dlogL D 1)]

end GlobalTheory.Mean4
