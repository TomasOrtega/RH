import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CompactDense

/- English proof (translation)
Introduce `y`. Establish `hm : ∀ n, MeasurableSet (compactCovering X n)` using `fun n => (isCompact_compactCovering X n).isClosed.measurableSet`. Establish `hy : MemLp (y : X → ℂ) 2 μ` using `Lp.memLp y`. Set `u : ℕ → Lp ℂ 2 μ` to `fun n => (hy.indicator (hm n)).toLp _`. Establish `hu : ∀ n, (u n : X → ℂ) =ᵐ[μ] (compactCovering X n).indicator y` using `fun n => MemLp.coeFn_toLp _`.

Use `mem_closure_of_tendsto (f := u) (b := Filter.atTop) ?_ (Filter.Eventually.of_forall fun n => ?_)` and prove the remaining obligations. Establish `hi : Integrable (fun z => ‖(y : X → ℂ) z‖ ^ 2) μ` using `(memLp_two_iff_integrable_sq_norm hy.1).1 hy`. Establish `e : ∀ n, ‖u n - y‖ ^ 2 = ∫ z, (compactCovering X n)ᶜ.indicator (fun z => ‖(y : X → ℂ) z‖ ^ 2) z ∂μ`. Introduce `n`. Rewrite using `[← @inner_self_eq_norm_sq ℂ, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]`.

Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hu n, Lp.coeFn_sub (u n) y] with z h1 h2`. Rewrite using `[inner_self_eq_norm_sq, h2, Pi.sub_apply, h1]`. Apply the tactic sequence `by_cases hz : z ∈ compactCovering X n <;> simp [hz]`. Establish `h0 : Filter.Tendsto (fun n => ‖u n - y‖ ^ 2) Filter.atTop (nhds (∫ _z, (0 : ℝ) ∂μ))`.

Simplify using `only [e]`. Use `tendsto_integral_of_dominated_convergence _ (fun n => hi.1.indicator (hm n).compl) hi (fun n => Filter.Eventually.of_forall fun z => ?_) (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Use `(norm_indicator_le_norm_self _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules. Take `⟨N, hN⟩` from `exists_mem_compactCovering z`.

Use `tendsto_const_nhds.congr' ?_` and prove the remaining obligations. Use `filter_upwards [Filter.eventually_ge_atTop N] with n hn`. Establish `: z ∈ compactCovering X n` using `compactCovering_subset X hn hN`. Simplify using `[this]`. Rewrite `h0` using `[integral_zero]`.

Rewrite using `[tendsto_iff_norm_sub_tendsto_zero]`. Establish `h1` using `h0.sqrt`. Simplify using `using h1`. Use `⟨_, isCompact_compactCovering X n, ?_⟩ filter_upwards [hu n] with z h hz` and prove the remaining obligations. Simplify using `[h, hz]`.
-/
theorem dense_of_sigmaCompact {X : Type} [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) :
    Dense {y : Lp ℂ 2 μ | ∃ C : Set X, IsCompact C ∧ ∀ᵐ z ∂μ, z ∉ C → (y : X → ℂ) z = 0} := by
  intro y
  have hm : ∀ n, MeasurableSet (compactCovering X n) := fun n => (isCompact_compactCovering X n).isClosed.measurableSet
  have hy : MemLp (y : X → ℂ) 2 μ := Lp.memLp y
  let u : ℕ → Lp ℂ 2 μ := fun n => (hy.indicator (hm n)).toLp _
  have hu : ∀ n, (u n : X → ℂ) =ᵐ[μ] (compactCovering X n).indicator y := fun n => MemLp.coeFn_toLp _
  refine mem_closure_of_tendsto (f := u) (b := Filter.atTop) ?_ (Filter.Eventually.of_forall fun n => ?_)
  · have hi : Integrable (fun z => ‖(y : X → ℂ) z‖ ^ 2) μ := (memLp_two_iff_integrable_sq_norm hy.1).1 hy
    have e : ∀ n, ‖u n - y‖ ^ 2 = ∫ z, (compactCovering X n)ᶜ.indicator (fun z => ‖(y : X → ℂ) z‖ ^ 2) z ∂μ := by
      intro n
      rw [← @inner_self_eq_norm_sq ℂ, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
      refine integral_congr_ae ?_
      filter_upwards [hu n, Lp.coeFn_sub (u n) y] with z h1 h2
      rw [inner_self_eq_norm_sq, h2, Pi.sub_apply, h1]
      by_cases hz : z ∈ compactCovering X n <;> simp [hz]
    have h0 : Filter.Tendsto (fun n => ‖u n - y‖ ^ 2) Filter.atTop (nhds (∫ _z, (0 : ℝ) ∂μ)) := by
      simp only [e]
      refine tendsto_integral_of_dominated_convergence _ (fun n => hi.1.indicator (hm n).compl) hi
        (fun n => Filter.Eventually.of_forall fun z => ?_) (Filter.Eventually.of_forall fun z => ?_)
      · refine (norm_indicator_le_norm_self _ _).trans (le_of_eq ?_)
        simp
      · obtain ⟨N, hN⟩ := exists_mem_compactCovering z
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Filter.eventually_ge_atTop N] with n hn
        have : z ∈ compactCovering X n := compactCovering_subset X hn hN
        simp [this]
    rw [integral_zero] at h0
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 := h0.sqrt
    simpa using h1
  · refine ⟨_, isCompact_compactCovering X n, ?_⟩
    filter_upwards [hu n] with z h hz
    simp [h, hz]

/- English proof (translation)
Introduce `B`. Take `⟨h1, h2, h3, -⟩` from `GlobalTheory.CongTop.adelic_topology B.I`. Conclude with `dense_of_sigmaCompact _`.
-/
theorem dense_compact_support : ∀ B : RowsAut, Dense {y : B.I.L2 B.μf B.fund | ∃ C : Set B.I.GA, IsCompact C ∧ ∀ᵐ z ∂((B.I.muA B.μf).restrict B.fund), z ∉ C → (y : B.I.GA → ℂ) z = 0} := by
  intro B
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  exact dense_of_sigmaCompact _

end GlobalTheory.CompactDense
