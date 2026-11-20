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
Establish `h : IsIntegral V x` using `hx.tower_top`. Take `⟨y, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Conclude with `y.2`.
-/
theorem mem_of_isIntegral (V : ValuationSubring ℂ) {x : ℂ} (hx : IsIntegral ℤ x) : x ∈ V := by
  have h : IsIntegral V x := hx.tower_top
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact y.2

/- English proof (translation)
Rewrite `h`, the goal using `[← V.valuation_le_one_iff]`. Rewrite `h` using `[map_div₀, map_mul, map_pow, map_pow, hn, one_pow, one_mul, ← hu]`. Rewrite using `[map_div₀, map_pow]` and apply the resulting hypothesis.
-/
theorem mem_of_val (V : ValuationSubring ℂ) {n u Ω x : ℂ} (k : ℕ) (hn : V.valuation n = 1)
    (hu : V.valuation u = V.valuation Ω) (h : n ^ k * x / Ω ^ k ∈ V) : x / u ^ k ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_div₀, map_mul, map_pow, map_pow, hn, one_pow, one_mul, ← hu] at h
  rwa [map_div₀, map_pow]

/- English proof (translation)
Introduce `L β u V N hβ hβi hu hN z w hz hw hNz hNw`. Take `⟨Ω, hΩ⟩` from `IsAlgClosed.exists_pow_nat_eq (latticeCurve L).Δ (n := 12) (by norm_num)`. Establish `hN0 : 0 < N`. Break down `Nat.eq_zero_or_pos N with rfl | h` into its components or cases. Simplify using `at hN`.

Conclude with `h`. Establish `huΩ : V.valuation u = V.valuation Ω`. Rewrite `hu` using `[← hΩ, map_pow]`. Conclude with `(pow_left_inj₀ zero_le' zero_le' (by norm_num)).1 hu`. Establish `h` using `GlobalTheory.WpFam.LatTorsVal.main L β Ω N hβ hβi (hΩ.trans (latticeCurve_Δ L)) hN0`.

Conclude with `⟨mem_of_val V 3 hN huΩ (mem_of_isIntegral V (h.1 z hNz).2), mem_of_val V 2 hN huΩ (mem_of_isIntegral V (h.2 z w hz hw hNz hNw))⟩`.
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
