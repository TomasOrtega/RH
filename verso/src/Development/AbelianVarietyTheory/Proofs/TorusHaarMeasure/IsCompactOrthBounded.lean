import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FinCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Introduce `r X R`. Establish `h1 : IsClosed {x : Frame X.Ψ r | IsOrth X x}`. Simplify using `only [IsOrth, Set.ofPred_forall]`. Use `isClosed_iInter fun τ => isClosed_eq ?_ continuous_const` and prove the remaining obligations. Use `continuous_matrix fun a b => ?_` and prove the remaining obligations.

Simplify using `only [gram, hermC, col, mat, Matrix.of_apply]`. Use `fun_prop`. Establish `h2 : IsClosed {x : Frame X.Ψ r | ∀ τ a b, ‖x τ a b‖ ≤ R}`. Simplify using `only [Set.ofPred_forall]`. Use `isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun b => isClosed_le ?_ continuous_const` and prove the remaining obligations.

Use `fun_prop`. Use `Metric.isCompact_of_isClosed_isBounded (h1.inter h2) ?_` and prove the remaining obligations. Use `(Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := |R|)).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨-, hx⟩`. Rewrite using `[mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]`.

Introduce `τ`. Rewrite using `[pi_norm_le_iff_of_nonneg (abs_nonneg R)]`. Introduce `a`. Rewrite using `[pi_norm_le_iff_of_nonneg (abs_nonneg R)]`. Introduce `b`.

Conclude with `(hx τ a b).trans (le_abs_self R)`.
-/
theorem isCompact_orth_bounded :
    (∀ (r : ℕ) (X : Data E r) (R : ℝ),
      IsCompact {x : Frame X.Ψ r | IsOrth X x ∧ ∀ τ a b, ‖x τ a b‖ ≤ R}) := by
  intro r X R
  have h1 : IsClosed {x : Frame X.Ψ r | IsOrth X x} := by
    simp only [IsOrth, Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_eq ?_ continuous_const
    refine continuous_matrix fun a b => ?_
    simp only [gram, hermC, col, mat, Matrix.of_apply]
    fun_prop
  have h2 : IsClosed {x : Frame X.Ψ r | ∀ τ a b, ‖x τ a b‖ ≤ R} := by
    simp only [Set.ofPred_forall]
    refine isClosed_iInter fun τ => isClosed_iInter fun a => isClosed_iInter fun b =>
      isClosed_le ?_ continuous_const
    fun_prop
  refine Metric.isCompact_of_isClosed_isBounded (h1.inter h2) ?_
  refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := |R|)).subset ?_
  rintro x ⟨-, hx⟩
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro τ
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro a
  rw [pi_norm_le_iff_of_nonneg (abs_nonneg R)]
  intro b
  exact (hx τ a b).trans (le_abs_self R)

end GlobalTheory.FinCovol
