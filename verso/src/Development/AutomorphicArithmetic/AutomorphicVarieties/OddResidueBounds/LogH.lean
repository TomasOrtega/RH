import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.ZeroMemUnrHom
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealCounting.ClassC
import Development.AutomorphicArithmetic.AutomorphicVarieties.OddResidueBounds.LogDisc

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5 UpperTheory.V.Odd

/- English proof (translation)
Introduce `E _ _ N hN hE`. Take `⟨hd, hn⟩` from `UpperTheory.V.Odd.logDisc E N (by omega) hE`. Establish `hc` using `KStar.IdealCounting.log_classNumber_le E`. Establish `hd1 : (1 : ℝ) ≤ |(discr E : ℝ)|`. Conclude with `Int.one_le_abs (discr_ne_zero E)` after adjusting the coercions.

Establish `hd2 : |(discr E : ℝ)| ≤ (N : ℝ) ^ Module.finrank ℚ E`. Establish `h : (((discr E).natAbs : ℕ) : ℝ) ≤ (N : ℝ) ^ Module.finrank ℚ E` using `by exact_mod_cast hd`. Rewrite `h` using `[Nat.cast_natAbs, Int.cast_abs]`. Then use the resulting hypothesis. Establish `hN' : (2 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hn' : (Module.finrank ℚ E : ℝ) ≤ N` using `by exact_mod_cast hn`.

Establish `hn0 : (0 : ℝ) ≤ (Module.finrank ℚ E : ℝ)` using `Nat.cast_nonneg _`. Generalize the expression as in `Module.finrank ℚ E = n at *`. Establish `hL0 : 0 ≤ Real.log N` using `Real.log_nonneg (by linarith)`. Establish `hL1 : Real.log N ≤ N - 1` using `Real.log_le_sub_one_of_pos (by linarith)`. Establish `hD0 : 0 ≤ Real.log |(discr E : ℝ)|` using `Real.log_nonneg hd1`.

Establish `hD : Real.log |(discr E : ℝ)| ≤ n * Real.log N`. Rewrite using `[← Real.log_pow]`. Conclude with `Real.log_le_log (by linarith) hd2`. Establish `hnL : (n : ℝ) * Real.log N ≤ N * (N - 1)` using `mul_le_mul hn' hL1 hL0 (by linarith)`. Establish `h2 : Real.log (1 + Real.log |(discr E : ℝ)| / 2) ≤ 2 * Real.log N`.

Establish `e : 2 * Real.log N = Real.log ((N : ℝ) ^ 2)` using `by rw [Real.log_pow]; norm_num`. Rewrite using `[e]`. Apply `Real.log_le_log (by linarith)` to reduce the goal to its premises. Use the polynomial consequences of the given equalities and inequalities. Establish `h3` using `mul_le_mul_of_nonneg_left h2 hn0`.

Establish `h4` using `mul_nonneg hn0 hL0`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem UpperTheory.V.Odd.logH :
    ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 2 ≤ N → Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ) → Real.log (classNumber E) ≤ 3 * Module.finrank ℚ E * Real.log N := by
  intro E _ _ N hN hE
  obtain ⟨hd, hn⟩ := UpperTheory.V.Odd.logDisc E N (by omega) hE
  have hc := KStar.IdealCounting.log_classNumber_le E
  have hd1 : (1 : ℝ) ≤ |(discr E : ℝ)| := by
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  have hd2 : |(discr E : ℝ)| ≤ (N : ℝ) ^ Module.finrank ℚ E := by
    have h : (((discr E).natAbs : ℕ) : ℝ) ≤ (N : ℝ) ^ Module.finrank ℚ E := by exact_mod_cast hd
    rwa [Nat.cast_natAbs, Int.cast_abs] at h
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn' : (Module.finrank ℚ E : ℝ) ≤ N := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℚ E : ℝ) := Nat.cast_nonneg _
  generalize Module.finrank ℚ E = n at *
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hL1 : Real.log N ≤ N - 1 := Real.log_le_sub_one_of_pos (by linarith)
  have hD0 : 0 ≤ Real.log |(discr E : ℝ)| := Real.log_nonneg hd1
  have hD : Real.log |(discr E : ℝ)| ≤ n * Real.log N := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) hd2
  have hnL : (n : ℝ) * Real.log N ≤ N * (N - 1) := mul_le_mul hn' hL1 hL0 (by linarith)
  have h2 : Real.log (1 + Real.log |(discr E : ℝ)| / 2) ≤ 2 * Real.log N := by
    have e : 2 * Real.log N = Real.log ((N : ℝ) ^ 2) := by rw [Real.log_pow]; norm_num
    rw [e]
    apply Real.log_le_log (by linarith)
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 hn0
  have h4 := mul_nonneg hn0 hL0
  nlinarith
