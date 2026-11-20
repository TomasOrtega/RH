import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Ggeo.CompMem

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single k]`. Simplify using `[GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]`. Introduce `b _ hb`. Simplify using `[GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_eq_of_ne hb.symm]`. Simplify using the standard rewrite rules.
-/
theorem blockWeight_weight_apply {K : Type} [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
  · intro b _ hb
    simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_eq_of_ne hb.symm]
  · simp

/- English proof (translation)
Introduce `K _ _ ι _ P hP f hf b`. Take `⟨S, hS, rfl⟩` from `hP`. Use `letI := weightedGradedAlgebra ℤ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι)`. Use `weightedHomogeneousComponent_mem_of_mem ℤ _ ?_ hf b` and prove the remaining obligations. Use `Ideal.homogeneous_span _ S fun g hg => ?_` and prove the remaining obligations.

Take `⟨a, ha⟩` from `hS g hg`. Use `⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).2 fun m hm => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Rewrite using `[blockWeight_weight_apply]`. Conclude with `ha m (mem_support_iff.2 hm) k`.
-/
theorem comp_mem : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℤ)), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal P → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
  intro K _ _ ι _ P hP f hf b
  obtain ⟨S, hS, rfl⟩ := hP
  classical
  letI := weightedGradedAlgebra ℤ (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι)
  refine weightedHomogeneousComponent_mem_of_mem ℤ _ ?_ hf b
  refine Ideal.homogeneous_span _ S fun g hg => ?_
  obtain ⟨a, ha⟩ := hS g hg
  refine ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).2 fun m hm => ?_⟩
  funext k
  rw [blockWeight_weight_apply]
  exact ha m (mem_support_iff.2 hm) k

end GlobalTheory.CompanionTheory.Ggeo.CompMem
