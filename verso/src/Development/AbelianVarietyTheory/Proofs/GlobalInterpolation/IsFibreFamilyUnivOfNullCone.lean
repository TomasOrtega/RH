import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Establish `hae : ∀ b, ∀ᵐ x ∂(fib b), q x = b`. Introduce `b`. Use `measure_mono_null ?_ (h1 b)` and prove the remaining obligations. Introduce `x hx hx'`.

Conclude with `hx hx'.1`. Use `⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs _ => ?_⟩` and prove the remaining obligations. Use `measure_mono_null ?_ (h1 b)` and prove the remaining obligations. Introduce `x hx hx'`. Conclude with `hx ⟨hx'.1, trivial⟩`.

Establish `hμ : μ.restrict U = μ`. Apply `Measure.restrict_eq_self_of_ae_mem` to reduce the goal to its premises. Use `measure_mono_null ?_ h0` and prove the remaining obligations. Introduce `x hx`. Assume the negation of the conclusion as `hx'`.

Conclude with `hx (hU hx')`. Rewrite using `[← h2 φ hφ, hμ, Measure.restrict_univ]`. Establish `key : ∀ b0 : K, b0 ≠ 0 → ∃ D : Set K, D ∈ nhds b0 ∧ b0 ∈ D ∧ D ⊆ B ∧ (∀ b ∈ D, Integrable φ (fib b)) ∧ ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) D`. Introduce `b0 hb0`. Establish `hr : 0 < ‖b0‖` using `norm_pos_iff.mpr hb0`.

Establish `hD : IsClopen (Metric.ball b0 ‖b0‖)` using `IsUltrametricDist.isClopen_ball b0 _`. Use `set D := Metric.ball b0 ‖b0‖ with hDdef`. Establish `hD0 : ∀ t ∈ D, t ≠ 0`. Introduce and unpack `t ht rfl`. Simplify using `[hDdef] at ht`.

Establish `hE : IsClopen (q ⁻¹' D)` using `hD.preimage hq`. Set `ψ : V → ℝ` to `(q ⁻¹' D).indicator φ`. Establish `hψc : Continuous ψ` using `hE.continuous_indicator hc`. Establish `hψs : HasCompactSupport ψ`. Use `hcs.mono ?_` and prove the remaining obligations.

Introduce `x hx hx'`. Apply `hx` to reduce the goal to its premises. Simplify using `[ψ, Set.indicator, hx']`. Establish `hψt : tsupport ψ ⊆ U`. Establish `: tsupport ψ ⊆ q ⁻¹' D` using `closure_minimal Set.support_indicator_subset hE.isClosed`.

Introduce `x hx`. Conclude with `hU (hD0 _ (this hx))`. Take `⟨hi, hco⟩` from `h3 ψ hψc hψs hψt`. Establish `hDB : D ⊆ B` using `fun t ht => hB (hD0 t ht)`. Establish `heq : ∀ b ∈ D, ψ =ᵐ[fib b] φ`.

Introduce `b hb`. Use `filter_upwards [hae b] with x hx`. Establish `: x ∈ q ⁻¹' D` using `by show q x ∈ D`. Rewrite using `[hx]`. Conclude with `hb`.

Simplify using `[ψ, Set.indicator_of_mem this]`. Use `⟨D, Metric.ball_mem_nhds _ hr, Metric.mem_ball_self hr, hDB, fun b hb => ?_, ?_⟩` and prove the remaining obligations. Conclude with `(integrable_congr (heq b hb)).mp (hi b (hDB hb))`. Use `(hco.mono hDB).congr fun b hb => ?_` and prove the remaining obligations. Conclude with `(integral_congr_ae (heq b hb)).symm`.

Use `⟨fun b hb => ?_, fun b hb => ?_⟩` and prove the remaining obligations. Take `⟨D, -, hbD, -, hi, -⟩` from `key b hb`. Conclude with `hi b hbD`. Take `⟨D, hD, -, -, -, hco⟩` from `key b hb`. Conclude with `(hco.continuousAt hD).continuousWithinAt`.
-/
theorem isFibreFamily_univ_of_null_cone (K V : Type) [NormedField K] [IsUltrametricDist K]
    [MeasurableSpace K] [BorelSpace K] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (ν : Measure K) (q : V → K) (hq : Continuous q) (h0 : μ {x | q x = 0} = 0)
    (U : Set V) (B : Set K) (fib : K → Measure V) (hU : {x | q x ≠ 0} ⊆ U) (hB : {t | t ≠ 0} ⊆ B)
    (h : IsFibreFamily μ q id U ν B fib) :
    IsFibreFamily μ q id Set.univ ν {t | t ≠ 0} fib := by
  classical
  obtain ⟨h1, h2, h3⟩ := h
  have hae : ∀ b, ∀ᵐ x ∂(fib b), q x = b := by
    intro b
    refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx hx'.1
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hcs _ => ?_⟩
  · refine measure_mono_null ?_ (h1 b)
    intro x hx hx'
    exact hx ⟨hx'.1, trivial⟩
  · have hμ : μ.restrict U = μ := by
      apply Measure.restrict_eq_self_of_ae_mem
      refine measure_mono_null ?_ h0
      intro x hx
      by_contra hx'
      exact hx (hU hx')
    rw [← h2 φ hφ, hμ, Measure.restrict_univ]
  · have key : ∀ b0 : K, b0 ≠ 0 → ∃ D : Set K, D ∈ nhds b0 ∧ b0 ∈ D ∧ D ⊆ B ∧
        (∀ b ∈ D, Integrable φ (fib b)) ∧ ContinuousOn (fun b => ∫ v, φ v ∂(fib b)) D := by
      intro b0 hb0
      have hr : 0 < ‖b0‖ := norm_pos_iff.mpr hb0
      have hD : IsClopen (Metric.ball b0 ‖b0‖) := IsUltrametricDist.isClopen_ball b0 _
      set D := Metric.ball b0 ‖b0‖ with hDdef
      have hD0 : ∀ t ∈ D, t ≠ 0 := by
        rintro t ht rfl
        simp [hDdef] at ht
      have hE : IsClopen (q ⁻¹' D) := hD.preimage hq
      let ψ : V → ℝ := (q ⁻¹' D).indicator φ
      have hψc : Continuous ψ := hE.continuous_indicator hc
      have hψs : HasCompactSupport ψ := by
        refine hcs.mono ?_
        intro x hx hx'
        apply hx
        simp [ψ, Set.indicator, hx']
      have hψt : tsupport ψ ⊆ U := by
        have : tsupport ψ ⊆ q ⁻¹' D :=
          closure_minimal Set.support_indicator_subset hE.isClosed
        intro x hx
        exact hU (hD0 _ (this hx))
      obtain ⟨hi, hco⟩ := h3 ψ hψc hψs hψt
      have hDB : D ⊆ B := fun t ht => hB (hD0 t ht)
      have heq : ∀ b ∈ D, ψ =ᵐ[fib b] φ := by
        intro b hb
        filter_upwards [hae b] with x hx
        have : x ∈ q ⁻¹' D := by
          show q x ∈ D
          rw [hx]; exact hb
        simp [ψ, Set.indicator_of_mem this]
      refine ⟨D, Metric.ball_mem_nhds _ hr, Metric.mem_ball_self hr, hDB, fun b hb => ?_, ?_⟩
      · exact (integrable_congr (heq b hb)).mp (hi b (hDB hb))
      · refine (hco.mono hDB).congr fun b hb => ?_
        exact (integral_congr_ae (heq b hb)).symm
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · obtain ⟨D, -, hbD, -, hi, -⟩ := key b hb
      exact hi b hbD
    · obtain ⟨D, hD, -, -, -, hco⟩ := key b hb
      exact (hco.continuousAt hD).continuousWithinAt

end GlobalTheory
