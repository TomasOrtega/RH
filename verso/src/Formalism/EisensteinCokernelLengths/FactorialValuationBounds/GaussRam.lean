import Formalism.EisensteinCokernelLengths.RationalTailBound

open scoped ENNReal

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

/- English proof (translation)
Rewrite `hc` using `[Ideal.mem_span_singleton]`. Establish `h` using `(IsDiscreteValuationRing.addVal_le_iff_dvd (R := O)).2 hc`. Rewrite `h` using `[IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one]`. Then use the resulting hypothesis.
-/
private theorem le_addVal_of_mem_span_pow {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} {c : O}
    (hc : c ∈ Ideal.span {ϖ ^ e}) : (e : ℕ∞) ≤ IsDiscreteValuationRing.addVal O c := by
  rw [Ideal.mem_span_singleton] at hc
  have h := (IsDiscreteValuationRing.addVal_le_iff_dvd (R := O)).2 hc
  rwa [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    nsmul_one] at h

/- English proof (translation)
Use `le_antisymm ?_ (le_addVal_of_mem_span_pow hϖ h1)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Rewrite `h` using `[not_le]`. Apply `h2` to reduce the goal to its premises. Rewrite using `[Ideal.mem_span_singleton]`.

Apply `(IsDiscreteValuationRing.addVal_le_iff_dvd (R := O)).1` to reduce the goal to its premises. Rewrite using `[IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ, nsmul_one, Nat.cast_succ]`. Conclude with `Order.add_one_le_of_lt h`.
-/
private theorem addVal_eq_of_mem_span_pow_not_mem_succ {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} {c : O}
    (h1 : c ∈ Ideal.span {ϖ ^ e}) (h2 : c ∉ Ideal.span {ϖ ^ (e + 1)}) :
    IsDiscreteValuationRing.addVal O c = e := by
  refine le_antisymm ?_ (le_addVal_of_mem_span_pow hϖ h1)
  by_contra h
  rw [not_le] at h
  apply h2
  rw [Ideal.mem_span_singleton]
  apply (IsDiscreteValuationRing.addVal_le_iff_dvd (R := O)).1
  rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    nsmul_one, Nat.cast_succ]
  exact Order.add_one_le_of_lt h

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ e he x hx E N hN hE`. Take `⟨hmon, hdeg, hcoef, h0⟩` from `hE`. Establish `hc0 : IsDiscreteValuationRing.addVal O (E.coeff 0) = e` using `addVal_eq_of_mem_span_pow_not_mem_succ hϖ (hcoef 0 (by omega)) h0`. Establish `hcN : E.coeff N = 1`. Use `hmon.leadingCoeff` as an intermediate fact.

Rewrite `this` using `[Polynomial.leadingCoeff, hdeg]`. Then use the resulting hypothesis. Unfold `Formalism.NOK.gaussV`. Simplify using `only [Polynomial.coeff_coe]`. Apply `le_antisymm` to reduce the goal to its premises. Establish `h1` using `iInf_le (fun n : ℕ => ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal (x * n)) 0`.

Establish `h2` using `iInf_le (fun n : ℕ => ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal (x * n)) N`. Simplify using `only [hc0, hcN, AddValuation.map_one, ENat.toENNReal_zero, ENat.toENNReal_coe, Nat.cast_zero, mul_zero, ENNReal.ofReal_zero, add_zero, zero_add] at h1 h2`. Break down `le_total (e : ℝ) (x * N) with h | h` into its components or cases. Rewrite using `[min_eq_left h, ENNReal.ofReal_natCast]`. Conclude with `h1`.

Rewrite using `[min_eq_right h]`. Conclude with `h2`. Apply `le_iInf` to reduce the goal to its premises. Introduce `n`. Break down `lt_trichotomy n N with h | h | h` into its components or cases.

Establish `hv` using `le_addVal_of_mem_span_pow hϖ (hcoef n h)`. Combine the equalities or inequalities in the displayed calculation. Substitute `h` using the available equality. Rewrite using `[hcN, AddValuation.map_one, ENat.toENNReal_zero, zero_add]`. Conclude with `ENNReal.ofReal_le_ofReal (min_le_right _ _)`.

Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact h)]`. Simplify using the standard rewrite rules.
-/
theorem gaussValEisenstein : GaussEisRam := by
  intro O _ _ _ ϖ hϖ e he x hx E N hN hE
  obtain ⟨hmon, hdeg, hcoef, h0⟩ := hE
  have hc0 : IsDiscreteValuationRing.addVal O (E.coeff 0) = e :=
    addVal_eq_of_mem_span_pow_not_mem_succ hϖ (hcoef 0 (by omega)) h0
  have hcN : E.coeff N = 1 := by
    have := hmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at this
  unfold Formalism.NOK.gaussV
  simp only [Polynomial.coeff_coe]
  apply le_antisymm
  · have h1 := iInf_le (fun n : ℕ => ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) +
      ENNReal.ofReal (x * n)) 0
    have h2 := iInf_le (fun n : ℕ => ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) +
      ENNReal.ofReal (x * n)) N
    simp only [hc0, hcN, AddValuation.map_one, ENat.toENNReal_zero, ENat.toENNReal_coe,
      Nat.cast_zero, mul_zero, ENNReal.ofReal_zero, add_zero, zero_add] at h1 h2
    rcases le_total (e : ℝ) (x * N) with h | h
    · rw [min_eq_left h, ENNReal.ofReal_natCast]
      exact h1
    · rw [min_eq_right h]
      exact h2
  · apply le_iInf
    intro n
    rcases lt_trichotomy n N with h | h | h
    · have hv := le_addVal_of_mem_span_pow hϖ (hcoef n h)
      calc ENNReal.ofReal (min (e : ℝ) (x * N)) ≤ ENNReal.ofReal (e : ℝ) :=
            ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = ((e : ℕ∞) : ℝ≥0∞) := by rw [ENNReal.ofReal_natCast, ENat.toENNReal_coe]
        _ ≤ ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) :=
            ENat.toENNReal_le.2 hv
        _ ≤ _ := le_self_add
    · subst h
      rw [hcN, AddValuation.map_one, ENat.toENNReal_zero, zero_add]
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact h)]
      simp

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
