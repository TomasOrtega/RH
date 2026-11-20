import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChartEqsOfParts

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `d S T c O hST hS hT`. Take `⟨o, a⟩` from `S`. Take `⟨o', b⟩` from `T`. Simplify using `only at hST`. Substitute `hST` using the available equality.

Use `⟨⟨o, fun k w x => c * a k w x + b k w x⟩, rfl, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i w`. Conclude with `(contDiffOn_const.mul (hS i w)).add (hT i w)`. Introduce `u x`. Simplify using `only [SOp.app, Finset.mul_sum, ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Introduce `x ξ`. Simplify using `only [SOp.symb, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem symbol_operator_linear_holds : SOpLin := by
  intro d S T c O hST hS hT
  obtain ⟨o, a⟩ := S
  obtain ⟨o', b⟩ := T
  simp only at hST
  subst hST
  refine ⟨⟨o, fun k w x => c * a k w x + b k w x⟩, rfl, ?_, ?_, ?_⟩
  · intro i w
    exact (contDiffOn_const.mul (hS i w)).add (hT i w)
  · intro u x
    simp only [SOp.app, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_
    ring
  · intro x ξ
    simp only [SOp.symb, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    ring

end

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
