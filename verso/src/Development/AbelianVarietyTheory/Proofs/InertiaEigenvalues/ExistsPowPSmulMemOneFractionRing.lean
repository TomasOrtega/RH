import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Simplify by unfolding definitions. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem padicCoeff_exists_pow_smul_mem_one :
    ∀ {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O],
    PadicCoeff p O → ∀ y : FractionRing O,
    ∃ n, y ∈ (1 : Submodule O (FractionRing O)).comap (LinearMap.lsmul O _ ((p : O) ^ n)) := by
  intro p O _ _ _ _ hP y
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hdvd : ϖ ∣ (p : O) := by
    have h := hP.p_mem
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h
    exact h
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) y
  dsimp only
  have hb : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  have hbk : (b : O) ∣ (p : O) ^ k := by
    rw [hu]
    exact (Units.mul_left_dvd).mpr (pow_dvd_pow_of_dvd hdvd k)
  obtain ⟨c, hc⟩ := hbk
  refine ⟨k, ?_⟩
  rw [Submodule.mem_comap, LinearMap.lsmul_apply, Submodule.mem_one]
  refine ⟨c * a, ?_⟩
  rw [Algebra.smul_def, hc, map_mul, map_mul, mul_assoc, mul_left_comm, IsLocalization.mk'_spec']

end GlobalTheory
