import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StandardSlopeBound.NablaBasis

noncomputable section

namespace PI.SlopeSteps

open MvPolynomial Formalism.GradedWeylDivisibility

/- English proof (translation)
The claim follows from `(fockQPos _ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)).2 (hwNe ℚ N N le_rfl ν)`.
-/
theorem hwNormPos {N : ℕ} (ν : Fin N → ℕ) : 0 < fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) :=
  (fockQPos _ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν)).2 (hwNe ℚ N N le_rfl ν)

/- English proof (translation)
Break down `Nat.eq_zero_or_pos N with h0 | h0` into its components or cases. Rewrite using `[hk h0, pow_zero]`. Conclude with `one_pos`. Conclude with `pow_pos (by exact_mod_cast h0) k`.
-/
theorem natPowPos (N k : ℕ) (hk : N = 0 → k = 0) : (0 : ℚ) < (N : ℚ) ^ k := by
  rcases Nat.eq_zero_or_pos N with h0 | h0
  · rw [hk h0, pow_zero]; exact one_pos
  · exact pow_pos (by exact_mod_cast h0) k

/- English proof (translation)
Introduce and unpack `rfl`. Simplify using the standard rewrite rules.
-/
theorem sumNuZero {N : ℕ} (ν : Fin N → ℕ) : N = 0 → ∑ s, ν s = 0 := by
  rintro rfl
  simp

/- English proof (translation)
Introduce `N ν μ hν ⟨r, e, hr, hμ⟩`. Take `⟨r', ⟨e'⟩⟩` from `hT4 N ν`. Take `⟨hrr, hdet⟩` from `hT3 N ν r r' e e' hν`. Substitute `hrr` using the available equality. Establish `hlow` using `hT2 N ν r e' hν`.

Establish `hpos` using `hwNormPos ν`. Establish `hNpow` using `natPowPos N (∑ s, ν s) (sumNuZero ν)`. Establish `hPpos : (0 : ℚ) < ((∏ s, (ν s).factorial : ℕ) : ℚ)`. Conclude with `Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _)` after adjusting the coercions. Use `set h := fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) with hh`.

Use `set A : ℚ := ((∏ s, (ν s).factorial : ℕ) : ℚ) / ((N : ℚ) ^ (∑ s, ν s) * h) with hAdef`. Establish `hA : 0 < A` using `div_pos hPpos (mul_pos hNpow hpos)`. Use `set D := (gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)).det with hDdef`. Use `set D' := (gramOf ν fun i => (e' i : MvPolynomial (Fin N × Fin N) ℤ)).det with hD'def`. Establish `hD'pos : 0 < D'` using `lt_of_lt_of_le (pow_pos hA r) hlow`.

Establish `hDeq : D = D'⁻¹` using `eq_inv_of_mul_eq_one_left hdet`. Establish `hDle : D ≤ (A ^ r)⁻¹` using `by rw [hDeq]; exact inv_anti₀ (pow_pos hA r) hlow`. Establish `hDpos : 0 < D` using `by rw [hDeq]; exact inv_pos.mpr hD'pos`. Establish `hstd : (PI.stdGram ν e).det = D` using `rfl`. Rewrite using `[hμ, hstd]`.

Establish `hDr : (0 : ℝ) < (D : ℝ)` using `by exact_mod_cast hDpos`. Establish `hDler : (D : ℝ) ≤ ((A : ℝ) ^ r)⁻¹` using `by exact_mod_cast hDle`. Establish `hlog : Real.log (D : ℝ) ≤ -((r : ℝ) * Real.log (A : ℝ))`. Combine the equalities or inequalities in the displayed calculation. Establish `hrpos : (0 : ℝ) < r` using `by exact_mod_cast hr`.

Establish `hlogA : Real.log (A : ℝ) = -((∑ l, (ν l : ℝ)) * Real.log N + Real.log (cNu ν))`. Establish `hP : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ)` using `Finset.prod_pos fun l _ => by exact_mod_cast Nat.factorial_pos _`. Establish `hNr : (0 : ℝ) < (N : ℝ) ^ (∑ s, ν s)` using `by exact_mod_cast hNpow`. Establish `hhr : (0 : ℝ) < (h : ℝ)` using `by exact_mod_cast hpos`. Establish `hAeq : (A : ℝ) = (∏ l, ((ν l).factorial : ℝ)) / ((N : ℝ) ^ (∑ s, ν s) * (h : ℝ))`.

Rewrite using `[hAdef]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : cNu ν = (h : ℝ) / ∏ l, ((ν l).factorial : ℝ)` using `rfl`. Rewrite using `[hAeq, hc, Real.log_div hP.ne' (mul_pos hNr hhr).ne', Real.log_mul hNr.ne' hhr.ne', Real.log_div hhr.ne' hP.ne', Real.log_pow]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← hlogA, le_div_iff₀ hrpos]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem stdSlopeLow_of (hT2 : NablaGramLow) (hT3 : GramDual) (hT4 : NablaBasis) : PI.StdSlopeLow := by
  intro N ν μ hν ⟨r, e, hr, hμ⟩
  obtain ⟨r', ⟨e'⟩⟩ := hT4 N ν
  obtain ⟨hrr, hdet⟩ := hT3 N ν r r' e e' hν
  subst hrr
  have hlow := hT2 N ν r e' hν
  have hpos := hwNormPos ν
  have hNpow := natPowPos N (∑ s, ν s) (sumNuZero ν)
  have hPpos : (0 : ℚ) < ((∏ s, (ν s).factorial : ℕ) : ℚ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.mpr fun s _ => Nat.factorial_ne_zero _)
  set h := fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) with hh
  set A : ℚ := ((∏ s, (ν s).factorial : ℕ) : ℚ) / ((N : ℚ) ^ (∑ s, ν s) * h) with hAdef
  have hA : 0 < A := div_pos hPpos (mul_pos hNpow hpos)
  set D := (gramOf ν fun i => (e i : MvPolynomial (Fin N × Fin N) ℤ)).det with hDdef
  set D' := (gramOf ν fun i => (e' i : MvPolynomial (Fin N × Fin N) ℤ)).det with hD'def
  have hD'pos : 0 < D' := lt_of_lt_of_le (pow_pos hA r) hlow
  have hDeq : D = D'⁻¹ := eq_inv_of_mul_eq_one_left hdet
  have hDle : D ≤ (A ^ r)⁻¹ := by rw [hDeq]; exact inv_anti₀ (pow_pos hA r) hlow
  have hDpos : 0 < D := by rw [hDeq]; exact inv_pos.mpr hD'pos
  have hstd : (PI.stdGram ν e).det = D := rfl
  rw [hμ, hstd]
  have hDr : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  have hDler : (D : ℝ) ≤ ((A : ℝ) ^ r)⁻¹ := by exact_mod_cast hDle
  have hlog : Real.log (D : ℝ) ≤ -((r : ℝ) * Real.log (A : ℝ)) := by
    calc Real.log (D : ℝ) ≤ Real.log (((A : ℝ) ^ r)⁻¹) := Real.log_le_log hDr hDler
      _ = -((r : ℝ) * Real.log (A : ℝ)) := by rw [Real.log_inv, Real.log_pow]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogA : Real.log (A : ℝ) = -((∑ l, (ν l : ℝ)) * Real.log N + Real.log (cNu ν)) := by
    have hP : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ) :=
      Finset.prod_pos fun l _ => by exact_mod_cast Nat.factorial_pos _
    have hNr : (0 : ℝ) < (N : ℝ) ^ (∑ s, ν s) := by exact_mod_cast hNpow
    have hhr : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hpos
    have hAeq : (A : ℝ) = (∏ l, ((ν l).factorial : ℝ)) / ((N : ℝ) ^ (∑ s, ν s) * (h : ℝ)) := by
      rw [hAdef]; push_cast; ring
    have hc : cNu ν = (h : ℝ) / ∏ l, ((ν l).factorial : ℝ) := rfl
    rw [hAeq, hc, Real.log_div hP.ne' (mul_pos hNr hhr).ne', Real.log_mul hNr.ne' hhr.ne',
      Real.log_div hhr.ne' hP.ne', Real.log_pow]
    push_cast
    ring
  rw [← hlogA, le_div_iff₀ hrpos]
  nlinarith

end PI.SlopeSteps
