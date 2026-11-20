import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real Filter Topology

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem LimitInEpsilon.proof : LimitInEpsilon.Statement := by
  intro n P Q W W0 e' C1 H
  obtain ⟨hP, hQ, hW, hb⟩ := H
  have hε : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hP' : Tendsto P (𝓝[>] 0) (𝓝 (P 0)) := hP
  have hQ' : Tendsto Q (𝓝[>] 0) (𝓝 (Q 0)) := hQ
  have hL : Tendsto (fun ε => (n + 1 : ℝ) * ((e' - ε * C1) * Q ε - 1 / 2 * W ε))
      (𝓝[>] 0) (𝓝 ((n + 1 : ℝ) * ((e' - 0 * C1) * Q 0 - 1 / 2 * W0))) :=
    tendsto_const_nhds.mul
      (((tendsto_const_nhds.sub (hε.mul tendsto_const_nhds)).mul hQ').sub
        (tendsto_const_nhds.mul hW))
  have key : (n + 1 : ℝ) * ((e' - 0 * C1) * Q 0 - 1 / 2 * W0) ≤ P 0 :=
    le_of_tendsto_of_tendsto hL hP' hb
  have e : (n + 1 : ℝ) * ((e' - 0 * C1) * Q 0 - 1 / 2 * W0) =
      (n + 1) * (e' * Q 0 - W0 / 2) := by ring
  rw [e] at key
  exact key

end GroundTheory.Heights₂.Heights.LowerBound
