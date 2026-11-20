import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LogIntSphere
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem ballProd_subset_polydisc {n k : ℕ} (h : HermNorm n) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ (v : Fin n → ℂ) (j : Fin n), ‖v j‖ ≤ C * h.norm v) :
    ballProd h k ⊆ LogInt.polydisc _ C := by
  intro u hu
  simp only [LogInt.polydisc, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  intro ij
  exact (hC (fun j => u (ij.1, j)) ij.2).trans (mul_le_of_le_one_right hC0 (hu ij.1).le)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
