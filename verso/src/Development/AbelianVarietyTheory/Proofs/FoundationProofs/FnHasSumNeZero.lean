import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumReindexNat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumPowerSeriesInvOfConvergentStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCommonDenominatorEqMonomialMulPowerSerStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

/- English proof (translation)
Establish `: (2 * Real.pi * Complex.I * z / N) = ((2 * Real.pi / N : ℝ) : ℂ) * (Complex.I * z)` using `by push_cast; ring`. Rewrite using `[this, Complex.re_ofReal_mul]`. Simplify using `[Complex.mul_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fn_hsne_re (N : ℕ) (z : ℂ) :
    (2 * Real.pi * Complex.I * z / N).re = -(2 * Real.pi * z.im / N) := by
  have : (2 * Real.pi * Complex.I * z / N) = ((2 * Real.pi / N : ℝ) : ℂ) * (Complex.I * z) := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]
  simp [Complex.mul_re]
  ring

/- English proof (translation)
Establish `hNr : (0 : ℝ) < N` using `by exact_mod_cast hN`. Establish `hpi : 0 < Real.pi` using `Real.pi_pos`. Use `⟨-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi), ?_, ?_⟩` and prove the remaining obligations. Establish `hlog : Real.log ‖x‖ < -(2 * Real.pi * C / N)`. Rewrite using `[Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hx)]`.

Conclude with `hxr`. Establish `him : (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi)).im = -(N * Real.log ‖x‖) / (2 * Real.pi)`. Establish `: (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi)) = ((-(N : ℝ) / (2 * Real.pi) : ℝ) : ℂ) * (Complex.I * Complex.log x)` using `by push_cast; ring`. Rewrite using `[this, Complex.im_ofReal_mul]`. Simplify using `[Complex.mul_im, Complex.log_re]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[him]`. Rewrite using `[lt_div_iff₀ (by positivity)]`. Use `mul_lt_mul_of_pos_left hlog hNr` as an intermediate fact. Establish `e : (N : ℝ) * -(2 * Real.pi * C / N) = -(C * (2 * Real.pi))`.

Clear the denominators using the available nonvanishing facts. Use polynomial arithmetic with `[this, e]`. Establish `: 2 * Real.pi * Complex.I * (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi)) / N = Complex.log x`. Establish `hN' : (N : ℂ) ≠ 0` using `by exact_mod_cast hN.ne'`. Establish `hp : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast hpi.ne'`.

Clear the denominators using the available nonvanishing facts. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.exp_log hx]`.
-/
theorem fn_hsne_pre (N : ℕ) (hN : 0 < N) (C : ℝ) (x : ℂ) (hx : x ≠ 0)
    (hxr : ‖x‖ < Real.exp (-(2 * Real.pi * C / N))) :
    ∃ z : ℂ, C < z.im ∧ Complex.exp (2 * Real.pi * Complex.I * z / N) = x := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi), ?_, ?_⟩
  · have hlog : Real.log ‖x‖ < -(2 * Real.pi * C / N) := by
      rw [Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hx)]; exact hxr
    have him : (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi)).im
        = -(N * Real.log ‖x‖) / (2 * Real.pi) := by
      have : (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi))
          = ((-(N : ℝ) / (2 * Real.pi) : ℝ) : ℂ) * (Complex.I * Complex.log x) := by
        push_cast; ring
      rw [this, Complex.im_ofReal_mul]
      simp [Complex.mul_im, Complex.log_re]
      ring
    rw [him]
    rw [lt_div_iff₀ (by positivity)]
    have := mul_lt_mul_of_pos_left hlog hNr
    have e : (N : ℝ) * -(2 * Real.pi * C / N) = -(C * (2 * Real.pi)) := by
      field_simp
    nlinarith [this, e]
  · have : 2 * Real.pi * Complex.I * (-(N : ℂ) * Complex.I * Complex.log x / (2 * Real.pi)) / N
        = Complex.log x := by
      have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast hpi.ne'
      field_simp
      ring_nf
      rw [Complex.I_sq]; ring
    rw [this, Complex.exp_log hx]

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `Ω _ ε C φ h hD h0 hS`. Take `⟨N, n₀, a, hN, ha0, ha, hz⟩` from `GlobalTheory.T.hahnSeries_commonDenominator_eq_monomial_mul_powerSeries Ω h hD h0`. Establish `hNr : (0 : ℝ) < N` using `by exact_mod_cast hN`. Establish `hpi : 0 < Real.pi` using `Real.pi_pos`. Use `set b : ℕ → ℂ := fun k => ε (a k) with hb`.

Establish `hb0 : b 0 ≠ 0`. Simplify using `only [hb]`. Conclude with `(map_ne_zero ε).mpr ha0`. Establish `key : ∀ z : ℂ, C < z.im → HasSum (fun k : ℕ => b k * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) (φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N)))` using `fun z hzC => (fn_hasSum_reindex_nat Ω ε h N n₀ a z (φ z) hN ha hz).mp (hS z hzC)`. Use `set ρ : ℝ := Real.exp (-(2 * Real.pi * C / N)) with hρ`.

Establish `hρ0 : 0 < ρ` using `Real.exp_pos _`. Establish `hsum : ∀ x : ℂ, ‖x‖ < ρ → Summable fun n => b n * x ^ n`. Introduce `x hx`. Distinguish the cases in `hx0 : x = 0`. Substitute `hx0` using the available equality.

Apply `summable_of_ne_finset_zero (s := {0})` to reduce the goal to its premises. Introduce `n hn`. Establish `: n ≠ 0` using `by simpa using hn`. Simplify using `[zero_pow this]`. Take `⟨z, hzC, hzx⟩` from `fn_hsne_pre N hN C x hx0 hx`.

Use `key z hzC` as an intermediate fact. Rewrite `this` using `[hzx]`. Conclude with `this.summable`. Take `⟨ρ', hρ'0, hρ'⟩` from `GlobalTheory.T.hasSum_powerSeries_inv_of_convergent b ρ hρ0 hb0 hsum`. Use `⟨max C (-(N * Real.log ρ') / (2 * Real.pi)), fun z hzi => ?_⟩` and prove the remaining obligations.

Establish `hzC : C < z.im` using `lt_of_le_of_lt (le_max_left _ _) hzi`. Establish `hz2 : -(N * Real.log ρ') / (2 * Real.pi) < z.im` using `lt_of_le_of_lt (le_max_right _ _) hzi`. Use `set x := Complex.exp (2 * Real.pi * Complex.I * z / N) with hxdef`. Establish `hxn : ‖x‖ < ρ'`. Rewrite using `[hxdef, Complex.norm_exp, fn_hsne_re]`.

Rewrite using `[← Real.exp_log hρ'0, Real.exp_lt_exp]`. Rewrite `hz2` using `[div_lt_iff₀ (by positivity)]`. Rewrite using `[neg_lt, lt_div_iff₀ hNr]`. Use polynomial arithmetic with `[hz2]`. Establish `hne` using `(hρ' x hxn).1`.

Rewrite `hne` using `[(key z hzC).tsum_eq]`. Introduce `hφ`. Apply `hne` to reduce the goal to its premises. Rewrite using `[hφ, zero_mul]`.
-/
theorem fn_hasSum_ne_zero : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω),
    Den h → h ≠ 0 → HS ε C φ h → ∃ C' : ℝ, ∀ z : ℂ, C' < z.im → φ z ≠ 0 := by
  intro Ω _ ε C φ h hD h0 hS
  obtain ⟨N, n₀, a, hN, ha0, ha, hz⟩ := GlobalTheory.T.hahnSeries_commonDenominator_eq_monomial_mul_powerSeries Ω h hD h0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : 0 < Real.pi := Real.pi_pos
  set b : ℕ → ℂ := fun k => ε (a k) with hb
  have hb0 : b 0 ≠ 0 := by
    simp only [hb]; exact (map_ne_zero ε).mpr ha0

  have key : ∀ z : ℂ, C < z.im →
      HasSum (fun k : ℕ => b k * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k)
        (φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) := fun z hzC =>
    (fn_hasSum_reindex_nat Ω ε h N n₀ a z (φ z) hN ha hz).mp (hS z hzC)
  set ρ : ℝ := Real.exp (-(2 * Real.pi * C / N)) with hρ
  have hρ0 : 0 < ρ := Real.exp_pos _
  have hsum : ∀ x : ℂ, ‖x‖ < ρ → Summable fun n => b n * x ^ n := by
    intro x hx
    by_cases hx0 : x = 0
    · subst hx0
      apply summable_of_ne_finset_zero (s := {0})
      intro n hn
      have : n ≠ 0 := by simpa using hn
      simp [zero_pow this]
    · obtain ⟨z, hzC, hzx⟩ := fn_hsne_pre N hN C x hx0 hx
      have := key z hzC
      rw [hzx] at this
      exact this.summable
  obtain ⟨ρ', hρ'0, hρ'⟩ := GlobalTheory.T.hasSum_powerSeries_inv_of_convergent b ρ hρ0 hb0 hsum
  refine ⟨max C (-(N * Real.log ρ') / (2 * Real.pi)), fun z hzi => ?_⟩
  have hzC : C < z.im := lt_of_le_of_lt (le_max_left _ _) hzi
  have hz2 : -(N * Real.log ρ') / (2 * Real.pi) < z.im := lt_of_le_of_lt (le_max_right _ _) hzi
  set x := Complex.exp (2 * Real.pi * Complex.I * z / N) with hxdef
  have hxn : ‖x‖ < ρ' := by
    rw [hxdef, Complex.norm_exp, fn_hsne_re]
    rw [← Real.exp_log hρ'0, Real.exp_lt_exp]
    rw [div_lt_iff₀ (by positivity)] at hz2
    rw [neg_lt, lt_div_iff₀ hNr]
    nlinarith [hz2]
  have hne := (hρ' x hxn).1
  rw [(key z hzC).tsum_eq] at hne
  intro hφ
  apply hne
  rw [hφ, zero_mul]

end GlobalTheory
