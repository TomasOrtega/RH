import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InjectiveHolomorphicOpen.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U → IsOpen (f '' U)

/- English proof (translation)
Use `⟨Metric.isOpen_ball, ?_, ?_⟩` and prove the remaining obligations. Use `Differentiable.differentiableOn ?_` and prove the remaining obligations. Rewrite using `[differentiable_pi]`. Introduce `i`. Use `fin_cases i`.

Simplify using `using differentiable_apply (𝕜 := ℂ) (0 : Fin 2)`. Establish `hd : Differentiable ℂ (fun x : Fin 2 → ℂ => x 1 + x 0 ^ 2)` using `by fun_prop`. Conclude with `hd`. Introduce `s _ t _ hst`. Establish `h0 : s 0 = t 0` using `by simpa using congrFun hst 0`.

Establish `h1 : s 1 + s 0 ^ 2 = t 1 + t 0 ^ 2` using `by simpa using congrFun hst 1`. Use function extensionality and compare the values at `i`. Use `fin_cases i`. Conclude with `h0`. Simplify using `only [Fin.mk_one]`.

Rewrite `h1` using `[h0]`. Conclude with `add_right_cancel h1`.
-/
theorem InjectiveHolomorphicOpen.hypotheses_inhabited :
    IsOpen (Metric.ball (0 : Fin 2 → ℂ) 1) ∧
      DifferentiableOn ℂ (fun t : Fin 2 → ℂ => ![t 0, t 1 + t 0 ^ 2]) (Metric.ball 0 1) ∧
      Set.InjOn (fun t : Fin 2 → ℂ => ![t 0, t 1 + t 0 ^ 2]) (Metric.ball 0 1) := by
  refine ⟨Metric.isOpen_ball, ?_, ?_⟩
  · refine Differentiable.differentiableOn ?_
    rw [differentiable_pi]
    intro i
    fin_cases i
    · simpa using differentiable_apply (𝕜 := ℂ) (0 : Fin 2)
    · have hd : Differentiable ℂ (fun x : Fin 2 → ℂ => x 1 + x 0 ^ 2) := by fun_prop
      exact hd
  · intro s _ t _ hst
    have h0 : s 0 = t 0 := by simpa using congrFun hst 0
    have h1 : s 1 + s 0 ^ 2 = t 1 + t 0 ^ 2 := by simpa using congrFun hst 1
    funext i
    fin_cases i
    · exact h0
    · simp only [Fin.mk_one]
      rw [h0] at h1
      exact add_right_cancel h1

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
