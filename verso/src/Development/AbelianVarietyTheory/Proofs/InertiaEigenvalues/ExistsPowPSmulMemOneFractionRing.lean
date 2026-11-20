import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2
open Formalism.NG (KO)

namespace GlobalTheory

/- English proof (translation)
Introduce `p O _ _ _ _ hP y`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Establish `hdvd : ϖ ∣ (p : O)`. Establish `h` using `hP.p_mem`. Rewrite `h` using `[hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]`.

Conclude with `h`. Take `⟨⟨a, b⟩, rfl⟩` from `IsLocalization.mk'_surjective (nonZeroDivisors O) y`. Simplify using `only`. Establish `hb : (b : O) ≠ 0` using `nonZeroDivisors.coe_ne_zero b`. Take `⟨k, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ`.

Establish `hbk : (b : O) ∣ (p : O) ^ k`. Rewrite using `[hu]`. Conclude with `(Units.mul_left_dvd).mpr (pow_dvd_pow_of_dvd hdvd k)`. Take `⟨c, hc⟩` from `hbk`. Use `⟨k, ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.mem_comap, LinearMap.lsmul_apply, Submodule.mem_one]`. Use `⟨c * a, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, hc, map_mul, map_mul, mul_assoc, mul_left_comm, IsLocalization.mk'_spec']`.
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
