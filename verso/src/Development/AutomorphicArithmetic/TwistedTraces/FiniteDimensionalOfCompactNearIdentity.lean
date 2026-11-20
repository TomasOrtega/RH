import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

/- English proof (translation)
Introduce `H _ _ _ T S hT hS`. Establish `hcl : IsClosed {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖}` using `isClosed_le (by fun_prop) (by fun_prop)`. Establish `hS' : ∀ v ∈ S.topologicalClosure, ‖T v - v‖ ≤ 1 / 2 * ‖v‖`. Introduce `v hv`. Establish `: closure (S : Set H) ⊆ {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖}` using `closure_minimal (fun w hw => hS w hw) hcl`.

Conclude with `this hv`. Use `haveI : CompleteSpace S.topologicalClosure := S.isClosed_topologicalClosure.completeSpace_coe`. Set `f : S.topologicalClosure →L[ℂ] H` to `T.comp S.topologicalClosure.subtypeL`. Establish `hf : ∀ x : S.topologicalClosure, ‖x‖ ≤ ((2 : NNReal) : ℝ) * ‖f x‖`. Introduce `x`.

Establish `h1` using `hS' x.1 x.2`. Establish `h2 : ‖(x : H)‖ ≤ ‖T x‖ + ‖T x - x‖`. Establish `: (x : H) = T x - (T x - x)` using `by abel`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : ‖x‖ = ‖(x : H)‖` using `rfl`.

Establish `h4 : f x = T x` using `rfl`. Rewrite using `[h3, h4]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hanti : AntilipschitzWith 2 f` using `f.antilipschitz_of_bound hf`.

Establish `hemb : IsClosedEmbedding f` using `hanti.isClosedEmbedding f.uniformContinuous`. Take `⟨K, hK, hKsub⟩` from `IsCompactOperator.image_closedBall_subset_compact (f := (T : H →ₗ[ℂ] H)) hT 1`. Establish `hc : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1)`. Use `(hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_` and prove the remaining obligations. Introduce `x hx`.

Apply `hKsub` to reduce the goal to its premises. Use `⟨(x : H), ?_, rfl⟩` and prove the remaining obligations. Rewrite `hx`, the goal using `[mem_closedBall_zero_iff]`. Conclude with `hx`. Use `haveI : FiniteDimensional ℂ S.topologicalClosure := FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos hc`.

Conclude with `Submodule.finiteDimensional_of_le S.le_topologicalClosure`.
-/
theorem UpperTheory.finiteDimensional_of_compact_near_identity :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (S : Submodule ℂ H), IsCompactOperator T → (∀ v ∈ S, ‖T v - v‖ ≤ 1 / 2 * ‖v‖) → FiniteDimensional ℂ S := by
  intro H _ _ _ T S hT hS
  have hcl : IsClosed {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hS' : ∀ v ∈ S.topologicalClosure, ‖T v - v‖ ≤ 1 / 2 * ‖v‖ := by
    intro v hv
    have : closure (S : Set H) ⊆ {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖} :=
      closure_minimal (fun w hw => hS w hw) hcl
    exact this hv
  haveI : CompleteSpace S.topologicalClosure :=
    S.isClosed_topologicalClosure.completeSpace_coe
  let f : S.topologicalClosure →L[ℂ] H := T.comp S.topologicalClosure.subtypeL
  have hf : ∀ x : S.topologicalClosure, ‖x‖ ≤ ((2 : NNReal) : ℝ) * ‖f x‖ := by
    intro x
    have h1 := hS' x.1 x.2
    have h2 : ‖(x : H)‖ ≤ ‖T x‖ + ‖T x - x‖ := by
      have : (x : H) = T x - (T x - x) := by abel
      calc ‖(x : H)‖ = ‖T x - (T x - x)‖ := congrArg norm this
        _ ≤ _ := norm_sub_le _ _
    have h3 : ‖x‖ = ‖(x : H)‖ := rfl
    have h4 : f x = T x := rfl
    rw [h3, h4]
    push_cast
    linarith
  have hanti : AntilipschitzWith 2 f := f.antilipschitz_of_bound hf
  have hemb : IsClosedEmbedding f := hanti.isClosedEmbedding f.uniformContinuous
  obtain ⟨K, hK, hKsub⟩ := IsCompactOperator.image_closedBall_subset_compact (f := (T : H →ₗ[ℂ] H)) hT 1
  have hc : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1) := by
    refine (hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_
    intro x hx
    apply hKsub
    refine ⟨(x : H), ?_, rfl⟩
    rw [mem_closedBall_zero_iff] at hx ⊢
    exact hx
  haveI : FiniteDimensional ℂ S.topologicalClosure :=
    FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos hc
  exact Submodule.finiteDimensional_of_le S.le_topologicalClosure
