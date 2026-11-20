import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory
open scoped InnerProductSpace

/- English proof (translation)
Introduce `k hk a`. Take `⟨m, rfl⟩ : ∃ m, k = m + 1` from `⟨k - 1, by omega⟩`. Establish `h2 : 2 * (m + 1) - 2 = 2 * m` using `by omega`. Establish `h1 : m + 1 - 1 = m` using `by omega`. Rewrite using `[h2, h1, (h0 a m).1, real_inner_self_eq_norm_sq, ← pow_mul]`.

Establish `hpos : (2 * (m : ℝ) + 1) ≠ 0` using `by positivity`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem FibrePushforward.proof (h0 : SphereMoment.Statement) : FibrePushforward.Statement := by
  intro k hk a
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have h2 : 2 * (m + 1) - 2 = 2 * m := by omega
  have h1 : m + 1 - 1 = m := by omega
  rw [h2, h1, (h0 a m).1, real_inner_self_eq_norm_sq, ← pow_mul]
  have hpos : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end GroundTheory.Heights₂.Heights.FlagBundles
