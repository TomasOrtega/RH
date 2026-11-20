import Mathlib
import Formalism.IncomingBounds.IncomingBound
import Formalism.IncomingBounds.FlowDegreeBounds.MaxFlowValueAttained

open scoped BigOperators
open Formalism.IncomingBounds

/- English proof (translation)
Introduce `l d _ hl D hD`. Establish `hl1 : 1 ≤ l` using `by omega`. Take `⟨x, hx, hmax⟩` from `FlowLoadBounds.exists_opt_flow hl1 D hD`. Take `⟨σ, hσ, hsum⟩` from `FlowLoadBounds.strong hl1 D hD`. Use `⟨⟨x, hx, (FlowLoadBounds.maxFlow_eq hx hmax).symm⟩, σ, hσ, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fnum, ← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun s _ => by ring`.
-/
theorem UpperTheory.exists_maxFlow_attained_and_isOptDual :
    ∀ (l d : ℕ) [NeZero d], 3 ≤ l → ∀ D : ZMod d → ℝ, 0 ≤ D →
    (∃ x, IsFlow l d D x ∧ flowVal d x = maxFlow l d D) ∧ ∃ sig, IsOptDual l d D sig := by
  intro l d _ hl D hD
  have hl1 : 1 ≤ l := by omega
  obtain ⟨x, hx, hmax⟩ := FlowLoadBounds.exists_opt_flow hl1 D hD
  obtain ⟨σ, hσ, hsum⟩ := FlowLoadBounds.strong hl1 D hD
  refine ⟨⟨x, hx, (FlowLoadBounds.maxFlow_eq hx hmax).symm⟩, σ, hσ, ?_⟩
  rw [Fnum, ← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring
