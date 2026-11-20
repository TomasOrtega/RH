import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNProd

/- English proof (translation)
Introduce `Ω _ ε C φ ψ h h' H H' z hz`. Use `set e : ℚ → ℂ := fun r => Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) with he`. Use `set a : ℚ → ℂ := fun r => ε (h.coeff r) * e r with ha`. Use `set b : ℚ → ℂ := fun r => ε (h'.coeff r) * e r with hb`. Establish `hA : HasSum a (φ z)` using `H z hz`.

Establish `hB : HasSum b (ψ z)` using `H' z hz`. Establish `hAn : Summable fun r => ‖a r‖` using `summable_norm_iff.2 hA.summable`. Establish `hBn : Summable fun r => ‖b r‖` using `summable_norm_iff.2 hB.summable`. Establish `hP : HasSum (fun p : ℚ × ℚ => a p.1 * b p.2) (φ z * ψ z)` using `hA.mul hB (summable_mul_of_summable_norm hAn hBn)`. Establish `hF` using `hP.tsum_fiberwise (fun p : ℚ × ℚ => p.1 + p.2)`.

Use `hF.congr_fun ?_` and prove the remaining obligations. Introduce `s`. Establish `hexp : ∀ p : ℚ × ℚ, p.1 + p.2 = s → a p.1 * b p.2 = ε (h.coeff p.1) * ε (h'.coeff p.2) * e s`. Introduce `p hp`. Simplify using `only [ha, hb, he, ← hp]`.

Establish `: Complex.exp (2 * Real.pi * Complex.I * ((p.1 + p.2 : ℚ) : ℂ) * z) = Complex.exp (2 * Real.pi * Complex.I * (p.1 : ℂ) * z) * Complex.exp (2 * Real.pi * Complex.I * (p.2 : ℂ) * z)`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[tsum_subtype (f := fun p : ℚ × ℚ => a p.1 * b p.2)]`. Rewrite using `[tsum_eq_sum (s := Finset.antidiagonal h.isPWO_support h'.isPWO_support s)]`. Simplify using `only [HahnSeries.coeff_mul, map_sum, map_mul, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun p hp => ?_` and prove the remaining obligations. Rewrite `hp` using `[Finset.mem_antidiagonal]`. Rewrite using `[Set.indicator_of_mem (by simpa using hp.2.2)]`. Conclude with `(hexp p hp.2.2).symm`. Introduce `p hp`.

Distinguish the cases in `hs : p.1 + p.2 = s`. Rewrite using `[Set.indicator_of_mem (by simpa using hs), hexp p hs]`. Rewrite `hp` using `[Finset.mem_antidiagonal]`. Simplify using `only [HahnSeries.mem_support, not_and] at hp`. Distinguish the cases in `h1 : h.coeff p.1 = 0`.

Simplify using `[h1]`. Establish `h2 : h'.coeff p.2 = 0`. Assume the negation of the conclusion as `h2`. Conclude with `hp h1 h2 hs`. Simplify using `[h2]`.

Conclude with `Set.indicator_of_notMem (by simpa using hs) _`.
-/
theorem hs_mul : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω),
    HS ε C φ h → HS ε C ψ h' → HS ε C (φ * ψ) (h * h') := by
  intro Ω _ ε C φ ψ h h' H H' z hz
  set e : ℚ → ℂ := fun r => Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * z) with he
  set a : ℚ → ℂ := fun r => ε (h.coeff r) * e r with ha
  set b : ℚ → ℂ := fun r => ε (h'.coeff r) * e r with hb
  have hA : HasSum a (φ z) := H z hz
  have hB : HasSum b (ψ z) := H' z hz
  have hAn : Summable fun r => ‖a r‖ := summable_norm_iff.2 hA.summable
  have hBn : Summable fun r => ‖b r‖ := summable_norm_iff.2 hB.summable
  have hP : HasSum (fun p : ℚ × ℚ => a p.1 * b p.2) (φ z * ψ z) :=
    hA.mul hB (summable_mul_of_summable_norm hAn hBn)
  have hF := hP.tsum_fiberwise (fun p : ℚ × ℚ => p.1 + p.2)
  refine hF.congr_fun ?_
  intro s
  have hexp : ∀ p : ℚ × ℚ, p.1 + p.2 = s → a p.1 * b p.2 = ε (h.coeff p.1) * ε (h'.coeff p.2) * e s := by
    intro p hp
    simp only [ha, hb, he, ← hp]
    have : Complex.exp (2 * Real.pi * Complex.I * ((p.1 + p.2 : ℚ) : ℂ) * z) =
        Complex.exp (2 * Real.pi * Complex.I * (p.1 : ℂ) * z) * Complex.exp (2 * Real.pi * Complex.I * (p.2 : ℂ) * z) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  rw [tsum_subtype (f := fun p : ℚ × ℚ => a p.1 * b p.2)]
  rw [tsum_eq_sum (s := Finset.antidiagonal h.isPWO_support h'.isPWO_support s)]
  · simp only [HahnSeries.coeff_mul, map_sum, map_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_antidiagonal] at hp
    rw [Set.indicator_of_mem (by simpa using hp.2.2)]
    exact (hexp p hp.2.2).symm
  · intro p hp
    by_cases hs : p.1 + p.2 = s
    · rw [Set.indicator_of_mem (by simpa using hs), hexp p hs]
      rw [Finset.mem_antidiagonal] at hp
      simp only [HahnSeries.mem_support, not_and] at hp
      by_cases h1 : h.coeff p.1 = 0
      · simp [h1]
      · have h2 : h'.coeff p.2 = 0 := by
          by_contra h2; exact hp h1 h2 hs
        simp [h2]
    · exact Set.indicator_of_notMem (by simpa using hs) _

end GlobalTheory.FNProd
