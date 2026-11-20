import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMinimalOfForallDivPowTwelve
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

/- English proof (translation)
Introduce `p F _ _ w W u hp hI hΔ`. Establish `hmem : ∀ y : F, y ∈ w.valuationSubringAtPrime F ↔ w.valuation F y ≤ 1`. Introduce `y`. Rewrite using `[HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]`. Both sides reduce to the same expression.

Use `GlobalTheory.isMinimal_of_forall_div_pow_twelve _ F W hI ?_` and prove the remaining obligations. Introduce `x hx0 hx`. Assume the negation of the conclusion as `hnu`. Establish `hxF : (x : F) ≠ 0` using `fun h => hx0 (Subtype.ext h)`. Establish `hx1 : w.valuation F (x : F) < 1`.

Use `lt_of_le_of_ne ((hmem _).1 x.2) (fun h => hnu ?_)` and prove the remaining obligations. Establish `hi : (x : F)⁻¹ ∈ w.valuationSubringAtPrime F`. Rewrite using `[hmem, map_inv₀, h, inv_one]`. Conclude with `IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hxF))`. Establish `hu : w.valuation F ((u : w.valuationSubringAtPrime F) : F) = 1`.

Establish `h1` using `(hmem _).1 (u : w.valuationSubringAtPrime F).2`. Establish `h2` using `(hmem _).1 ((u⁻¹ : (w.valuationSubringAtPrime F)ˣ) : w.valuationSubringAtPrime F).2`. Establish `h3 : w.valuation F ((u : w.valuationSubringAtPrime F) : F) * w.valuation F (((u⁻¹ : (w.valuationSubringAtPrime F)ˣ) : w.valuationSubringAtPrime F) : F) = 1`. Rewrite using `[← map_mul, ← MulMemClass.coe_mul, Units.mul_inv]`. Simplify using the standard rewrite rules.

Use `le_antisymm h1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Take `⟨y, hy⟩` from `hx`. Establish `hy1` using `(hmem _).1 y.2`. Establish `hyx : (y : F) * (x : F) ^ 12 = W.Δ`.

Establish `: (y : F) = W.Δ / (x : F) ^ 12` using `hy`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts. Establish `hv` using `congrArg (w.valuation F) (hyx.trans hΔ)`. Rewrite `hv` using `[map_mul, map_mul, hu, Valuation.map_neg, map_pow, map_pow, one_mul]`.

Establish `hpv : w.valuation F (p : F) = w.intValuation (p : 𝓞 F)`. Rewrite using `[← w.valuation_of_algebraMap (K := F)]`. Simplify using the standard rewrite rules. Establish `hp' : WithZero.exp (-(3 : ℤ)) < w.valuation F (p : F)`. Rewrite using `[hpv]`.

Assume the negation of the conclusion as `h`. Conclude with `hp ((w.intValuation_le_pow_iff_mem _ 3).1 (by simpa using h))`. Establish `hle : w.valuation F (p : F) ^ 3 ≤ w.valuation F (x : F) ^ 12`. Rewrite using `[← hv]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hvx0 : w.valuation F (x : F) ≠ 0` using `by simpa using hxF`. Establish `hvp0 : w.valuation F (p : F) ≠ 0` using `(lt_of_le_of_lt zero_le' hp').ne'`. Rewrite `hle`, `hx1` using `[← WithZero.exp_log hvx0]`. Rewrite `hle`, `hp'` using `[← WithZero.exp_log hvp0]`. Rewrite `hle` using `[← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_le_exp]`.

Rewrite `hp'` using `[WithZero.exp_lt_exp]`. Rewrite `hx1` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Simplify using `only [nsmul_eq_mul] at hle`. Move the coercions through the operations in `at hle`. Use linear arithmetic over natural numbers and integers.
-/
theorem isMinimal_of_discr_eq_unit_mul_neg_cube : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (W : WeierstrassCurve F) (u : (w.valuationSubringAtPrime F)ˣ), (p : 𝓞 F) ∉ w.asIdeal ^ 3 → W.IsIntegral (w.valuationSubringAtPrime F) → W.Δ = ((u : w.valuationSubringAtPrime F) : F) * -(p : F) ^ 3 → W.IsMinimal (w.valuationSubringAtPrime F) := by
  intro p F _ _ w W u hp hI hΔ
  have hmem : ∀ y : F, y ∈ w.valuationSubringAtPrime F ↔ w.valuation F y ≤ 1 := by
    intro y
    rw [HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
    rfl
  refine GlobalTheory.isMinimal_of_forall_div_pow_twelve _ F W hI ?_
  intro x hx0 hx
  by_contra hnu
  have hxF : (x : F) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hx1 : w.valuation F (x : F) < 1 := by
    refine lt_of_le_of_ne ((hmem _).1 x.2) (fun h => hnu ?_)
    have hi : (x : F)⁻¹ ∈ w.valuationSubringAtPrime F := by
      rw [hmem, map_inv₀, h, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ hxF))
  have hu : w.valuation F ((u : w.valuationSubringAtPrime F) : F) = 1 := by
    have h1 := (hmem _).1 (u : w.valuationSubringAtPrime F).2
    have h2 := (hmem _).1 ((u⁻¹ : (w.valuationSubringAtPrime F)ˣ) : w.valuationSubringAtPrime F).2
    have h3 : w.valuation F ((u : w.valuationSubringAtPrime F) : F) *
        w.valuation F (((u⁻¹ : (w.valuationSubringAtPrime F)ˣ) : w.valuationSubringAtPrime F) : F) = 1 := by
      rw [← map_mul, ← MulMemClass.coe_mul, Units.mul_inv]; simp
    refine le_antisymm h1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = _ := h3.symm
      _ ≤ _ * 1 := mul_le_mul_right h2 _
      _ = _ := mul_one _
  obtain ⟨y, hy⟩ := hx
  have hy1 := (hmem _).1 y.2
  have hyx : (y : F) * (x : F) ^ 12 = W.Δ := by
    have : (y : F) = W.Δ / (x : F) ^ 12 := hy
    rw [this]; field_simp
  have hv := congrArg (w.valuation F) (hyx.trans hΔ)
  rw [map_mul, map_mul, hu, Valuation.map_neg, map_pow, map_pow, one_mul] at hv
  have hpv : w.valuation F (p : F) = w.intValuation (p : 𝓞 F) := by
    rw [← w.valuation_of_algebraMap (K := F)]; simp
  have hp' : WithZero.exp (-(3 : ℤ)) < w.valuation F (p : F) := by
    rw [hpv]
    by_contra h
    exact hp ((w.intValuation_le_pow_iff_mem _ 3).1 (by simpa using h))
  have hle : w.valuation F (p : F) ^ 3 ≤ w.valuation F (x : F) ^ 12 := by
    rw [← hv]
    calc _ ≤ 1 * _ := mul_le_mul_left hy1 _
      _ = _ := one_mul _
  have hvx0 : w.valuation F (x : F) ≠ 0 := by simpa using hxF
  have hvp0 : w.valuation F (p : F) ≠ 0 := (lt_of_le_of_lt zero_le' hp').ne'
  rw [← WithZero.exp_log hvx0] at hle hx1
  rw [← WithZero.exp_log hvp0] at hle hp'
  rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_le_exp] at hle
  rw [WithZero.exp_lt_exp] at hp'
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx1
  simp only [nsmul_eq_mul] at hle
  push_cast at hle
  omega

end GlobalTheory.CMModel
