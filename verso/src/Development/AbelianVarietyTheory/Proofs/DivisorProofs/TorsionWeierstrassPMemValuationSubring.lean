import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionNonrealMultiplier
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel.TorsMemVal

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem mem_of_isIntegral (V : ValuationSubring ℂ) {x : ℂ} (hx : IsIntegral ℤ x) : x ∈ V := by
  have h : IsIntegral V x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact y.2

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
theorem mem_of_val (V : ValuationSubring ℂ) {n u Ω x : ℂ} (k : ℕ) (hn : V.valuation n = 1)
    (hu : V.valuation u = V.valuation Ω) (h : n ^ k * x / Ω ^ k ∈ V) : x / u ^ k ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_div₀, map_mul, map_pow, map_pow, hn, one_pow, one_mul, ← hu] at h
  rwa [map_div₀, map_pow]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. Simplify using the standard rewrite rules.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem main : ∀ (L : PeriodPair) (β u : ℂ) (V : ValuationSubring ℂ) (N : ℕ), MulStable L β → β.im ≠ 0 → V.valuation u ^ 12 = V.valuation (latticeCurve L).Δ → V.valuation (N : ℂ) = 1 → ∀ z w, z ∉ L.lattice → w ∉ L.lattice → (N : ℂ) * z ∈ L.lattice → (N : ℂ) * w ∈ L.lattice → L.derivWeierstrassP z / u ^ 3 ∈ V ∧ (L.weierstrassP z - L.weierstrassP w) / u ^ 2 ∈ V := by
  intro L β u V N hβ hβi hu hN z w hz hw hNz hNw
  obtain ⟨Ω, hΩ⟩ := IsAlgClosed.exists_pow_nat_eq (latticeCurve L).Δ (n := 12) (by norm_num)
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · simp at hN
    · exact h
  have huΩ : V.valuation u = V.valuation Ω := by
    rw [← hΩ, map_pow] at hu
    exact (pow_left_inj₀ zero_le' zero_le' (by norm_num)).1 hu
  have h := GlobalTheory.WpFam.LatTorsVal.main L β Ω N hβ hβi (hΩ.trans (latticeCurve_Δ L)) hN0
  exact ⟨mem_of_val V 3 hN huΩ (mem_of_isIntegral V (h.1 z hNz).2),
    mem_of_val V 2 hN huΩ (mem_of_isIntegral V (h.2 z w hz hw hNz hNw))⟩

end GlobalTheory.CMModel.TorsMemVal
