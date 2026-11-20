import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ O _ _ _ _ hO φ`. Use `haveI := hO.ring`. Use `continuous_of_continuousAt_zero φ ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero]`. Introduce `s hs`.

Take `⟨n, hn⟩` from `(isAdic_iff.mp hO.adic).2 s hs`. Establish `hball : Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) ∈ nhds (0 : ℤ_[p])`. Apply `Metric.closedBall_mem_nhds` to reduce the goal to its premises. Establish `: (0 : ℝ) < p` using `by exact_mod_cast (Fact.out : p.Prime).pos`. Check the signs of the components of the expression.

Use `Filter.mem_map.mpr (Filter.mem_of_superset hball ?_)` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Metric.mem_closedBall, dist_zero_right, PadicInt.norm_le_pow_iff_mem_span_pow]`. Take `⟨a, rfl⟩` from `Ideal.mem_span_singleton'.mp hx`. Apply `hn` to reduce the goal to its premises.

Use `show φ (a * (p : ℤ_[p]) ^ n) ∈ ((IsLocalRing.maximalIdeal O) ^ n : Ideal O)`. Rewrite using `[map_mul, map_pow, map_natCast]`. Conclude with `Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hO.p_mem n)`.
-/
theorem padicInt_ringHom_continuous_of_padicCoeff : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [TopologicalSpace O], PadicCoeff p O → ∀ φ : ℤ_[p] →+* O, Continuous φ := by
  intro p _ O _ _ _ _ hO φ
  haveI := hO.ring
  refine continuous_of_continuousAt_zero φ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨n, hn⟩ := (isAdic_iff.mp hO.adic).2 s hs
  have hball : Metric.closedBall (0 : ℤ_[p]) ((p : ℝ) ^ (-(n : ℤ))) ∈ nhds (0 : ℤ_[p]) := by
    apply Metric.closedBall_mem_nhds
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  refine Filter.mem_map.mpr (Filter.mem_of_superset hball ?_)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, PadicInt.norm_le_pow_iff_mem_span_pow] at hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hx
  apply hn
  show φ (a * (p : ℤ_[p]) ^ n) ∈ ((IsLocalRing.maximalIdeal O) ^ n : Ideal O)
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hO.p_mem n)

end GlobalTheory
