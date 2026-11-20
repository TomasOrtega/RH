import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPolyNonvanishDense
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

/- English proof (translation)
Introduce `e D hD`. Rewrite using `[dense_iff_inter_open]`. Introduce and unpack `U hU ⟨y₀, hy₀⟩`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[Set.not_nonempty_iff_eq_empty]`.

Take `⟨ε, hε, hball⟩` from `Metric.isOpen_iff.mp hU y₀ hy₀`. Establish `hzero : map (algebraMap ℚ ℂ) D = 0`. Use `funext_set (fun j => Metric.ball (y₀ j) ε) (fun j => infinite_of_mem_nhds (y₀ j) (Metric.ball_mem_nhds _ hε)) fun y hy => ?_` and prove the remaining obligations. Rewrite `hy` using `[← ball_pi y₀ hε]`. Establish `hyU` using `hball hy`.

Rewrite using `[map_zero, eval_map, ← aeval_def]`. Assume the negation of the conclusion as `hyD`. Conclude with `(Set.eq_empty_iff_forall_notMem.mp hne) y ⟨hyU, hyD⟩`. Conclude with `hD (map_injective _ (algebraMap ℚ ℂ).injective (by rw [hzero, map_zero]))`.
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
