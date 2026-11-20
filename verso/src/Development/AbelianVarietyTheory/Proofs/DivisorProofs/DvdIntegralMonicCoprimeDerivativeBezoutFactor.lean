import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ w P₀ hP hc Q₁ hQ`. Establish `hinj : Function.Injective (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))` using `IsFractionRing.injective (w.adicCompletionIntegers E) (w.adicCompletion E)`. Take `⟨g, hg⟩` from `IsIntegrallyClosed.eq_map_mul_C_of_dvd (w.adicCompletion E) hP hQ`. Establish `hPm : (P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))).Monic` using `hP.map _`. Establish `hQ0 : Q₁ ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hPm.ne_zero (zero_dvd_iff.mp hQ)`. Establish `hlc : Q₁.leadingCoeff ≠ 0` using `leadingCoeff_ne_zero.mpr hQ0`. Establish `hgm' : g.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = Q₁ * C Q₁.leadingCoeff⁻¹`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, mul_one]`. Use `_ = Q₁ * C Q₁.leadingCoeff⁻¹ := by rw [hg]`. Establish `hgmon : g.Monic`. Apply `Polynomial.monic_of_injective hinj` to reduce the goal to its premises. Rewrite using `[hgm']`.

Conclude with `monic_mul_leadingCoeff_inv hQ0`. Establish `hdvd : g ∣ P₀`. Rewrite using `[← map_dvd_map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) hinj hgmon]`. Conclude with `dvd_trans ⟨C Q₁.leadingCoeff, hg.symm⟩ hQ`. Take `⟨Q₂, hQ₂⟩` from `hdvd`.

Take `⟨a, b, hab⟩` from `hc`. Use `⟨g, Q₂, a * Q₂ + b * derivative Q₂, b * derivative g, Q₁.leadingCoeff, hlc, hQ₂, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hab` using `[hQ₂, derivative_mul]`. Take the linear combination `hab`. Conclude with `hg.symm.trans (mul_comm _ _)`.
-/
theorem monic_dvd_integral_factor_bezout : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (P₀ : (w.adicCompletionIntegers E)[X]), P₀.Monic →
    IsCoprime P₀ (derivative P₀) → ∀ Q₁ : (w.adicCompletion E)[X],
    Q₁ ∣ P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) →
    ∃ (Q₁₀ Q₂₀ A B : (w.adicCompletionIntegers E)[X]) (c : w.adicCompletion E), c ≠ 0 ∧ P₀ = Q₁₀ * Q₂₀ ∧
      A * Q₁₀ + B * Q₂₀ = 1 ∧ Q₁ = C c * Q₁₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
  intro E _ _ w P₀ hP hc Q₁ hQ
  have hinj : Function.Injective (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := IsFractionRing.injective (w.adicCompletionIntegers E) (w.adicCompletion E)
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (w.adicCompletion E) hP hQ
  have hPm : (P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))).Monic := hP.map _
  have hQ0 : Q₁ ≠ 0 := by
    rintro rfl
    exact hPm.ne_zero (zero_dvd_iff.mp hQ)
  have hlc : Q₁.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
  have hgm' : g.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = Q₁ * C Q₁.leadingCoeff⁻¹ := by
    calc _ = g.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) * C Q₁.leadingCoeff * C Q₁.leadingCoeff⁻¹ := by
          rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, mul_one]
      _ = Q₁ * C Q₁.leadingCoeff⁻¹ := by rw [hg]
  have hgmon : g.Monic := by
    apply Polynomial.monic_of_injective hinj
    rw [hgm']
    exact monic_mul_leadingCoeff_inv hQ0
  have hdvd : g ∣ P₀ := by
    rw [← map_dvd_map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) hinj hgmon]
    exact dvd_trans ⟨C Q₁.leadingCoeff, hg.symm⟩ hQ
  obtain ⟨Q₂, hQ₂⟩ := hdvd
  obtain ⟨a, b, hab⟩ := hc
  refine ⟨g, Q₂, a * Q₂ + b * derivative Q₂, b * derivative g, Q₁.leadingCoeff, hlc, hQ₂, ?_, ?_⟩
  · rw [hQ₂, derivative_mul] at hab
    linear_combination hab
  · exact hg.symm.trans (mul_comm _ _)

end GlobalTheory
