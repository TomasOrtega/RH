import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFDerivAtOfContinuousPartials

open scoped ContDiff Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `k F G hG hF t`. Use `hasFDerivAt_of_continuous_partials k F G (fun i t => ?_) hG t` and prove the remaining obligations. Establish `h0 : HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) (t i - t i)`. Rewrite using `[sub_self]`. Conclude with `hF i t`.

Establish `h1` using `h0.comp_sub_const (t i) (t i)`. Establish `hfun : (fun s : ℝ => F (Function.update t i s)) = fun s : ℝ => F (t + (s - t i) • Pi.single i 1)`. Use function extensionality and compare the values at `s`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hj]`. Rewrite using `[hfun]`.

Conclude with `h1`.
-/
theorem hasFDerivAt_of_continuous_coordinate_line_derivs :
    ∀ (k : ℕ) (F : (Fin k → ℝ) → ℂ) (G : Fin k → (Fin k → ℝ) → ℂ), (∀ i, Continuous (G i)) →
      (∀ i t, HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) 0) →
      ∀ t, HasFDerivAt F
        (∑ i, (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (G i t)) t := by
  intro k F G hG hF t
  refine hasFDerivAt_of_continuous_partials k F G (fun i t => ?_) hG t
  have h0 : HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (G i t) (t i - t i) := by
    rw [sub_self]
    exact hF i t
  have h1 := h0.comp_sub_const (t i) (t i)
  have hfun : (fun s : ℝ => F (Function.update t i s)) =
      fun s : ℝ => F (t + (s - t i) • Pi.single i 1) := by
    funext s
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · simp [hj]
  rw [hfun]
  exact h1

end GlobalTheory
