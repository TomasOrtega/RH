import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntSphere
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

/- English proof (translation)
Introduce `u hu`. Simplify using `only [LogInt.polydisc, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]`. Introduce `ij`. Conclude with `(hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)`.
-/
theorem ballProd_subset_polydisc {n k : ℕ} (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballProd h k ⊆ LogInt.polydisc _ C := by
  intro u hu
  simp only [LogInt.polydisc, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)

/- English proof (translation)
Introduce `n k δ h f hf _`. Take `⟨C, hC0, hC⟩` from `h.li_exists_coord_le`. Establish `e : nrmGroups h k = LogInt.normT h Finset.univ`. Use function extensionality and compare the values at `u ij`. Simplify using `[nrmGroups, LogInt.normT]`.

Rewrite using `[e]`. Conclude with `(LogInt.logNormT h C hC0 hC Finset.univ f hf).1.mono_set (ballProd_subset_polydisc h C hC0 hC)`.
-/
theorem MahlerIntegrand.proof : MahlerIntegrand.Statement := by
  intro n k δ h f hf _
  obtain ⟨C, hC0, hC⟩ := h.li_exists_coord_le
  have e : nrmGroups h k = LogInt.normT h Finset.univ := by
    funext u ij
    simp [nrmGroups, LogInt.normT]
  rw [e]
  exact (LogInt.logNormT h C hC0 hC Finset.univ f hf).1.mono_set (ballProd_subset_polydisc h C hC0 hC)

end GroundTheory.Heights₂.Heights
