import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.NormRepresentationLift.NormRepStepOfTrace
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscrB

noncomputable section

open scoped Classical ComplexConjugate

namespace PI.NRL

open NumberField Formalism.BasicNotions Formalism.FrobeniusOrbits Polynomial

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `haveI := D.host.isCMField_hostE`. Use `show D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = _`. Conclude with `NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x`.
-/
theorem star_emb (D : D7) (x : D.host.E) : D.host.φ₀ (star x) = conj (D.host.φ₀ x) := by
  haveI := D.host.isCMField_hostE
  show D.host.φ₀ (NumberField.IsCMField.complexConj D.host.E x) = _
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E D.host.φ₀ x

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Establish `h : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)` using `D.host.φ₀_mem`. Rewrite using `[star_emb, map_neg, h, map_mul, Complex.conj_I, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem star_sqrtMinusD (D : D7) : star D.host.sqrtMinusD = -D.host.sqrtMinusD := by
  apply D.host.φ₀.injective
  have h : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [star_emb, map_neg, h, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/- English proof (translation)
Establish `hd : D.host.d % 16 = 7` using `D.host.hyp.2.2.2.1`. Take `⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 4 * k` from `⟨(D.host.d + 1) / 4, by omega⟩`. Establish `hs : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E)` using `D.host.sqd_sq`. Establish `hk' : (D.host.d : D.host.E) + 1 = 4 * (k : D.host.E)` using `by exact_mod_cast hk`. Establish `hω : ((1 + D.host.sqrtMinusD) / 2) ^ 2 - (1 + D.host.sqrtMinusD) / 2 + (k : D.host.E) = 0`.

Take the linear combination `(1 / 4 : D.host.E) * hs - (1 / 4 : D.host.E) * hk'`. Establish `hint : IsIntegral ℤ ((1 + D.host.sqrtMinusD) / 2)`. Use `⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k : ℤ), by monicity!, ?_⟩` and prove the remaining obligations. Simplify using `using hω`. Use `⟨⟨(1 + D.host.sqrtMinusD) / 2, hint⟩, ?_⟩` and prove the remaining obligations.

Use `show (1 + D.host.sqrtMinusD) / 2 + star ((1 + D.host.sqrtMinusD) / 2) = 1`. Rewrite using `[star_div₀, star_add, star_one, star_sqrtMinusD, star_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem traceOne (D : D7) : TraceOne D := by
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d + 1 = 4 * k := ⟨(D.host.d + 1) / 4, by omega⟩
  have hs : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hk' : (D.host.d : D.host.E) + 1 = 4 * (k : D.host.E) := by exact_mod_cast hk
  have hω : ((1 + D.host.sqrtMinusD) / 2) ^ 2 - (1 + D.host.sqrtMinusD) / 2 + (k : D.host.E) = 0 := by
    linear_combination (1 / 4 : D.host.E) * hs - (1 / 4 : D.host.E) * hk'
  have hint : IsIntegral ℤ ((1 + D.host.sqrtMinusD) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k : ℤ), by monicity!, ?_⟩
    simpa using hω
  refine ⟨⟨(1 + D.host.sqrtMinusD) / 2, hint⟩, ?_⟩
  show (1 + D.host.sqrtMinusD) / 2 + star ((1 + D.host.sqrtMinusD) / 2) = 1
  rw [star_div₀, star_add, star_one, star_sqrtMinusD, star_ofNat]
  ring

end PI.NRL
