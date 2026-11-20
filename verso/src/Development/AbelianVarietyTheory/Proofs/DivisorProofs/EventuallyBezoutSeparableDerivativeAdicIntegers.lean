import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SepBezout

/- English proof (translation)
Take `⟨a, b, hb, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hI : Ideal.span {b} ≠ (0 : Ideal (𝓞 E))`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hb0`.

Use `Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq] at hw ⊢`. Assume the negation of the conclusion as `hd`. Apply `hw` to reduce the goal to its premises. Establish `h1 : w.valuation E (algebraMap (𝓞 E) E b) = 1` using `le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))`.

Rewrite using `[map_div₀, h1, div_one]`. Conclude with `w.valuation_le_one a`.
-/
theorem valuation_le_one_eventually {E : Type} [Field E] [NumberField E] (x : E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, w.valuation E x ≤ 1 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hI : Ideal.span {b} ≠ (0 : Ideal (𝓞 E)) := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hb0
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset fun w hw => ?_)
  simp only [Set.mem_setOf_eq] at hw ⊢
  by_contra hd
  apply hw
  have h1 : w.valuation E (algebraMap (𝓞 E) E b) = 1 :=
    le_antisymm (w.valuation_le_one b) (not_lt.1 fun h => hd ((w.valuation_lt_one_iff_dvd b).1 h))
  rw [map_div₀, h1, div_one]
  exact w.valuation_le_one a

/- English proof (translation)
Introduce `E _ _ P hP`. Take `⟨u₀, v₀, h⟩` from `hP`. Establish `key : ∀ f : E[X], ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ i, (f.map (algebraMap E (w.adicCompletion E))).coeff i ∈ w.adicCompletionIntegers E`. Introduce `f`. Use `filter_upwards [(Filter.eventually_all_finset f.support).2 (fun i _ => valuation_le_one_eventually (f.coeff i))] with w hw i`.

Rewrite using `[Polynomial.coeff_map]`. Distinguish the cases in `hi : i ∈ f.support`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Use `hw i hi` as an intermediate fact. Rewrite `this` using `[← HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`.

Conclude with `this`. Rewrite using `[Polynomial.notMem_support_iff.1 hi, map_zero]`. Conclude with `zero_mem _`. Use `filter_upwards [key u₀, key v₀] with w hu hv`. Use `⟨u₀.map (algebraMap E (w.adicCompletion E)), v₀.map (algebraMap E (w.adicCompletion E)), hu, hv, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, h, Polynomial.map_one]`.
-/
theorem bezout_eventually : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ u v : (w.adicCompletion E)[X],
      (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧ (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * P.map (algebraMap E (w.adicCompletion E)) + v * derivative (P.map (algebraMap E (w.adicCompletion E))) = 1 := by
  intro E _ _ P hP
  obtain ⟨u₀, v₀, h⟩ := hP
  have key : ∀ f : E[X], ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite,
      ∀ i, (f.map (algebraMap E (w.adicCompletion E))).coeff i ∈ w.adicCompletionIntegers E := by
    intro f
    filter_upwards [(Filter.eventually_all_finset f.support).2
      (fun i _ => valuation_le_one_eventually (f.coeff i))] with w hw i
    rw [Polynomial.coeff_map]
    by_cases hi : i ∈ f.support
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      have := hw i hi
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at this
      exact this
    · rw [Polynomial.notMem_support_iff.1 hi, map_zero]
      exact zero_mem _
  filter_upwards [key u₀, key v₀] with w hu hv
  refine ⟨u₀.map (algebraMap E (w.adicCompletion E)), v₀.map (algebraMap E (w.adicCompletion E)), hu, hv, ?_⟩
  rw [Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, h,
    Polynomial.map_one]

end GlobalTheory.BCT.SepBezout
