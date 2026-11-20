import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolyNonvanishDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Assume the negation of the conclusion and derive a contradiction. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem PolyNonvanishDense.proof : PolyNonvanishDense.Statement := by
  intro e D hD
  rw [dense_iff_inter_open]
  rintro U hU ⟨y₀, hy₀⟩
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU y₀ hy₀
  have hzero : map (algebraMap ℚ ℂ) D = 0 := by
    refine funext_set (fun j => Metric.ball (y₀ j) ε)
      (fun j => infinite_of_mem_nhds (y₀ j) (Metric.ball_mem_nhds _ hε)) fun y hy => ?_
    rw [← ball_pi y₀ hε] at hy
    have hyU := hball hy
    rw [map_zero, eval_map, ← aeval_def]
    by_contra hyD
    exact (Set.eq_empty_iff_forall_notMem.mp hne) y ⟨hyU, hyD⟩
  exact hD (map_injective _ (algebraMap ℚ ℂ).injective (by rw [hzero, map_zero]))

end GroundTheory.Heights₂.Heights.HilbertSamuel
