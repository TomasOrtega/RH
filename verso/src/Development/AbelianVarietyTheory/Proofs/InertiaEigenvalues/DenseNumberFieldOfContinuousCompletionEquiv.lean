import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNotMemMulValuationLeOneOfNe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory

open IsDedekindDomain.HeightOneSpectrum

/- English proof (translation)
The claim follows from `(A'.valuation_le_one_iff _).2 (mem_of_isIntegral_int A' (map_isIntegral_int (algebraMap E' Ω') (RingOfIntegers.isIntegral_coe m)))`.
-/
theorem valuationSubring_le_one_of_ringOfIntegers {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω']
    [Algebra E' Ω'] (A' : ValuationSubring Ω') (m : 𝓞 E') :
    A'.valuation (algebraMap E' Ω' (m : E')) ≤ 1 :=
  (A'.valuation_le_one_iff _).2
    (mem_of_isIntegral_int A' (map_isIntegral_int (algebraMap E' Ω') (RingOfIntegers.isIntegral_coe m)))

/- English proof (translation)
Take `⟨s, hs, hq⟩` from `GlobalTheory.exists_notMem_mul_valuation_le_one_of_ne w' (fun _ : Unit => t)`. Establish `hsle : w'.valuation E' (s : E') ≤ 1`. Rewrite using `[RingOfIntegers.coe_eq_algebraMap]`. Conclude with `w'.valuation_le_one (K := E') s`. Establish `hw : w'.valuation E' ((s : E') * t) < 1`.

Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hall : ∀ q : HeightOneSpectrum (𝓞 E'), q.valuation E' ((s : E') * t) ≤ 1`. Introduce `q`. Distinguish the cases in `hq' : q = w'`.

Substitute `hq'` using the available equality. Conclude with `hw.le`. Conclude with `hq q hq' ()`. Take `⟨m, hm⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one E' _ hall`. Establish `hmw : m ∈ w'.asIdeal`.

Rewrite using `[← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E')]`. Use `show w'.valuation E' (algebraMap (𝓞 E') E' m) < 1`. Rewrite using `[hm]`. Conclude with `hw`. Establish `h1` using `(hP m).2 hmw`.

Establish `h2 : A'.valuation (algebraMap E' Ω' (s : E')) = 1` using `le_antisymm (valuationSubring_le_one_of_ringOfIntegers A' s) (not_lt.1 (fun h => hs ((hP s).1 h)))`. Establish `hm' : ((m : 𝓞 E') : E') = (s : E') * t` using `by rw [← hm]`. Rewrite `h1` using `[hm', map_mul, map_mul, h2, one_mul]`. Conclude with `h1`.
-/
theorem valuationSubring_lt_one_of_placeOver {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω']
    [Algebra E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (hP : IsPlaceOver A' w')
    (t : E') (ht : w'.valuation E' t < 1) : A'.valuation (algebraMap E' Ω' t) < 1 := by
  obtain ⟨s, hs, hq⟩ := GlobalTheory.exists_notMem_mul_valuation_le_one_of_ne w' (fun _ : Unit => t)
  have hsle : w'.valuation E' (s : E') ≤ 1 := by
    rw [RingOfIntegers.coe_eq_algebraMap]; exact w'.valuation_le_one (K := E') s
  have hw : w'.valuation E' ((s : E') * t) < 1 := by
    rw [map_mul]
    calc w'.valuation E' (s : E') * w'.valuation E' t ≤ 1 * w'.valuation E' t := by gcongr
      _ < 1 := by rwa [one_mul]
  have hall : ∀ q : HeightOneSpectrum (𝓞 E'), q.valuation E' ((s : E') * t) ≤ 1 := by
    intro q
    by_cases hq' : q = w'
    · subst hq'; exact hw.le
    · exact hq q hq' ()
  obtain ⟨m, hm⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E' _ hall
  have hmw : m ∈ w'.asIdeal := by
    rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E')]
    show w'.valuation E' (algebraMap (𝓞 E') E' m) < 1
    rw [hm]; exact hw
  have h1 := (hP m).2 hmw
  have h2 : A'.valuation (algebraMap E' Ω' (s : E')) = 1 :=
    le_antisymm (valuationSubring_le_one_of_ringOfIntegers A' s) (not_lt.1 (fun h => hs ((hP s).1 h)))
  have hm' : ((m : 𝓞 E') : E') = (s : E') * t := by rw [← hm]
  rw [hm', map_mul, map_mul, h2, one_mul] at h1
  exact h1

/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic ℤ E' := ⟨fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ E').mpr (Algebra.IsAlgebraic.isAlgebraic x)⟩`. Use `haveI : Algebra.IsAlgebraic ℤ Ω' := Algebra.IsAlgebraic.trans ℤ E' Ω'`. Take `⟨n, hn, hint⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := ℤ) δ⁻¹).exists_integral_multiple`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations. Establish `hle` using `(A'.valuation_le_one_iff _).2 (mem_of_isIntegral_int A' hint)`.

Rewrite `hle` using `[zsmul_eq_mul, map_mul, map_inv₀]`. Establish `hd : A'.valuation δ ≠ 0` using `by simpa using hδ`. Rewrite using `[map_intCast]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_assoc, inv_mul_cancel₀ hd, mul_one]`.

Use `_ ≤ 1 * A'.valuation δ := by gcongr`. Use `_ = A'.valuation δ := one_mul _`.
-/
theorem exists_int_valuationSubring_le {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω']
    [Algebra E' Ω'] [Algebra.IsAlgebraic E' Ω'] (A' : ValuationSubring Ω') {δ : Ω'} (hδ : δ ≠ 0) :
    ∃ n : ℤ, n ≠ 0 ∧ A'.valuation (algebraMap E' Ω' (n : E')) ≤ A'.valuation δ := by
  haveI : Algebra.IsAlgebraic ℤ E' :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff ℤ ℚ E').mpr (Algebra.IsAlgebraic.isAlgebraic x)⟩
  haveI : Algebra.IsAlgebraic ℤ Ω' := Algebra.IsAlgebraic.trans ℤ E' Ω'
  obtain ⟨n, hn, hint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) δ⁻¹).exists_integral_multiple
  refine ⟨n, hn, ?_⟩
  have hle := (A'.valuation_le_one_iff _).2 (mem_of_isIntegral_int A' hint)
  rw [zsmul_eq_mul, map_mul, map_inv₀] at hle
  have hd : A'.valuation δ ≠ 0 := by simpa using hδ
  rw [map_intCast]
  calc A'.valuation (n : Ω') = A'.valuation (n : Ω') * (A'.valuation δ)⁻¹ * A'.valuation δ := by
        rw [mul_assoc, inv_mul_cancel₀ hd, mul_one]
    _ ≤ 1 * A'.valuation δ := by gcongr
    _ = A'.valuation δ := one_mul _

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ w E' Ω' _ _ _ _ _ A' w' hP j i hi hij y δ hδ`. Take `⟨n, hn, hnδ⟩` from `exists_int_valuationSubring_le (E' := E') A' hδ`. Use `set c : E' := (n : E') with hcdef`. Establish `hc : c ≠ 0` using `Int.cast_ne_zero.mpr hn`. Set `U : Set (w'.adicCompletion E')` to `{z | Valued.v ((z - algebraMap E' _ y) * (algebraMap E' (w'.adicCompletion E') c)⁻¹) < 1}`.

Establish `hU : IsOpen U`. Establish `h` using `(Valued.isOpen_ball (w'.adicCompletion E') 1).preimage ((continuous_sub_right (algebraMap E' (w'.adicCompletion E') y)).mul (continuous_const (y := (algebraMap E' (w'.adicCompletion E') c)⁻¹)))`. Use `h using 2 with z` and compare the differences between its conclusion and the goal. Simplify using `[U, Valuation.restrict_lt_iff_lt_embedding]`. Establish `hdense : DenseRange (i ∘ algebraMap E (w.adicCompletion E))` using `i.surjective.denseRange.comp (HeightOneSpectrum.denseRange_algebraMap E w) hi`.

Take `⟨x, hx⟩` from `hdense.exists_mem_open hU ⟨algebraMap E' _ y, by simp [U]⟩`. Use `⟨x, ?_⟩` and prove the remaining obligations. Establish `hx' : w'.valuation E' ((j x - y) * c⁻¹) < 1`. Establish `e : (i (algebraMap E _ x) - algebraMap E' (w'.adicCompletion E') y) * (algebraMap E' (w'.adicCompletion E') c)⁻¹ = algebraMap E' (w'.adicCompletion E') ((j x - y) * c⁻¹)`. Rewrite using `[hij, map_mul, map_sub, map_inv₀]`.

Establish `hx2 : (i ∘ algebraMap E (w.adicCompletion E)) x ∈ U` using `hx`. Simplify using `only [Function.comp, U, Set.mem_ofPred_eq] at hx2`. Rewrite `hx2` using `[e]`. Establish `hv : Valued.v (algebraMap E' (w'.adicCompletion E') ((j x - y) * c⁻¹)) = w'.valuation E' ((j x - y) * c⁻¹)` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w' _`. Rewrite `hx2` using `[hv]`.

Conclude with `hx2`. Establish `ht` using `valuationSubring_lt_one_of_placeOver A' w' hP _ hx'`. Establish `e2 : algebraMap E' Ω' y - algebraMap E' Ω' (j x) = -(algebraMap E' Ω' ((j x - y) * c⁻¹) * algebraMap E' Ω' c)`. Rewrite using `[← map_mul, ← map_sub, ← map_neg]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hcpos : 0 < A'.valuation (algebraMap E' Ω' c)`. Rewrite using `[zero_lt_iff]`. Simplify using `using hc`.

Rewrite using `[e2, Valuation.map_neg, map_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem approx_of_completion_equiv : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [Algebra.IsAlgebraic E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')), IsPlaceOver A' w' → ∀ (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E' _ (j x)) → ∀ (y : E') (δ : Ω'), δ ≠ 0 → ∃ x : E, A'.valuation (algebraMap E' Ω' y - algebraMap E' Ω' (j x)) < A'.valuation δ := by
  intro E _ _ w E' Ω' _ _ _ _ _ A' w' hP j i hi hij y δ hδ
  obtain ⟨n, hn, hnδ⟩ := exists_int_valuationSubring_le (E' := E') A' hδ
  set c : E' := (n : E') with hcdef
  have hc : c ≠ 0 := Int.cast_ne_zero.mpr hn
  let U : Set (w'.adicCompletion E') :=
    {z | Valued.v ((z - algebraMap E' _ y) * (algebraMap E' (w'.adicCompletion E') c)⁻¹) < 1}
  have hU : IsOpen U := by
    have h := (Valued.isOpen_ball (w'.adicCompletion E') 1).preimage
      ((continuous_sub_right (algebraMap E' (w'.adicCompletion E') y)).mul
        (continuous_const (y := (algebraMap E' (w'.adicCompletion E') c)⁻¹)))
    convert h using 2 with z
    simp [U, Valuation.restrict_lt_iff_lt_embedding]
  have hdense : DenseRange (i ∘ algebraMap E (w.adicCompletion E)) :=
    i.surjective.denseRange.comp (HeightOneSpectrum.denseRange_algebraMap E w) hi
  obtain ⟨x, hx⟩ := hdense.exists_mem_open hU ⟨algebraMap E' _ y, by simp [U]⟩
  refine ⟨x, ?_⟩
  have hx' : w'.valuation E' ((j x - y) * c⁻¹) < 1 := by
    have e : (i (algebraMap E _ x) - algebraMap E' (w'.adicCompletion E') y) *
        (algebraMap E' (w'.adicCompletion E') c)⁻¹ = algebraMap E' (w'.adicCompletion E') ((j x - y) * c⁻¹) := by
      rw [hij, map_mul, map_sub, map_inv₀]
    have hx2 : (i ∘ algebraMap E (w.adicCompletion E)) x ∈ U := hx
    simp only [Function.comp, U, Set.mem_ofPred_eq] at hx2
    rw [e] at hx2
    have hv : Valued.v (algebraMap E' (w'.adicCompletion E') ((j x - y) * c⁻¹)) = w'.valuation E' ((j x - y) * c⁻¹) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w' _
    rw [hv] at hx2
    exact hx2
  have ht := valuationSubring_lt_one_of_placeOver A' w' hP _ hx'
  have e2 : algebraMap E' Ω' y - algebraMap E' Ω' (j x) = -(algebraMap E' Ω' ((j x - y) * c⁻¹) * algebraMap E' Ω' c) := by
    rw [← map_mul, ← map_sub, ← map_neg]; congr 1; field_simp; ring
  have hcpos : 0 < A'.valuation (algebraMap E' Ω' c) := by
    rw [zero_lt_iff]; simpa using hc
  rw [e2, Valuation.map_neg, map_mul]
  calc _ < A'.valuation (algebraMap E' Ω' c) := mul_lt_of_lt_one_left hcpos ht
    _ ≤ A'.valuation δ := hnδ

end GlobalTheory
