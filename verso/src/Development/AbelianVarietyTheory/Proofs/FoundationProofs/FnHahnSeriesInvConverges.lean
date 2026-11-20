import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesAsRatHahnSeriesFractionalQStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHasSumReindexNat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumPowerSeriesInvOfConvergentStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCommonDenominatorEqMonomialMulPowerSerStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

/- English proof (translation)
Introduce `Ω _ ε C φ h hD hne hS`. Take `⟨N, n₀, a, hN, ha0, hcoef, hzero⟩` from `GlobalTheory.T.hahnSeries_commonDenominator_eq_monomial_mul_powerSeries Ω h hD hne`. Take `⟨Φ, hΦ1, hΦ0⟩` from `GlobalTheory.T.powerSeries_as_rat_hahnSeries_fractional_q Ω N hN`. Use `set p : PowerSeries Ω := PowerSeries.mk a with hpdef`. Establish `hp0 : PowerSeries.constantCoeff p ≠ 0` using `by simpa [p] using ha0`.

Use `set q : PowerSeries Ω := p⁻¹ with hqdef`. Establish `hdiv : ∀ (r : ℚ) (m : ℤ) (k : ℕ), r - (m : ℚ) / N = (k : ℚ) / N ↔ r = ((m + k : ℤ) : ℚ) / N`. Introduce `r m k`. Rewrite using `[sub_eq_iff_eq_add]`. Use `push_cast`.

Apply the tactic sequence `constructor <;> intro hr <;> rw [hr] <;> ring`. Establish `hh : h = HahnSeries.single ((n₀ : ℚ) / N) (1 : Ω) * Φ p`. Use extensionality with `r`. Rewrite using `[HahnSeries.coeff_single_mul, one_mul]`. Distinguish the cases in `hr : ∃ k : ℕ, r = ((n₀ + k : ℤ) : ℚ) / N`.

Take `⟨k, rfl⟩` from `hr`. Rewrite using `[hcoef k, (hdiv _ n₀ k).2 rfl, hΦ1]`. Simplify using `[p]`. Use `push_neg at hr`. Rewrite using `[hzero r hr, hΦ0]`.

Introduce `k hk`. Conclude with `hr k ((hdiv r n₀ k).1 hk)`. Use `set g : HahnSeries ℚ Ω := HahnSeries.single (((-n₀ : ℤ) : ℚ) / N) (1 : Ω) * Φ q with hgdef`. Establish `hg : h⁻¹ = g`. Use `symm`.

Apply `eq_inv_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[hh, mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul, hqdef, PowerSeries.mul_inv_cancel _ hp0, map_one, mul_one, mul_one]`. Establish `: (n₀ : ℚ) / N + ((-n₀ : ℤ) : ℚ) / N = 0` using `by push_cast; ring`. Rewrite using `[this, HahnSeries.single_zero_one]`. Establish `hgc : ∀ k : ℕ, g.coeff (((-n₀ + k : ℤ) : ℚ) / N) = PowerSeries.coeff k q`.

Introduce `k`. Rewrite using `[hgdef, HahnSeries.coeff_single_mul, one_mul, (hdiv _ (-n₀) k).2 rfl, hΦ1]`. Establish `hgz : ∀ r : ℚ, (∀ k : ℕ, r ≠ ((-n₀ + k : ℤ) : ℚ) / N) → g.coeff r = 0`. Introduce `r hr`. Rewrite using `[hgdef, HahnSeries.coeff_single_mul, one_mul]`.

Apply `hΦ0` to reduce the goal to its premises. Introduce `k hk`. Conclude with `hr k ((hdiv r (-n₀) k).1 hk)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`.

Use `⟨N, hN, fun r hr => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `H`. Use `push_neg at H`. Conclude with `hr (hgz r fun k hk => H _ hk)`. Use `set A : ℕ → ℂ := fun k => ε (a k) with hAdef`.

Establish `hA0 : A 0 ≠ 0` using `(map_ne_zero ε).2 ha0`. Establish `hnorm : ∀ z : ℂ, ‖Complex.exp (2 * Real.pi * Complex.I * z / N)‖ = Real.exp (-(2 * Real.pi * z.im / N))`. Introduce `z`. Rewrite using `[Complex.norm_exp]`. Use `congr 1`.

Establish `hNc : ((N : ℂ)) = ((N : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[hNc, Complex.div_ofReal_re]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hred : ∀ z : ℂ, C < z.im → HasSum (fun k : ℕ => A k * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) (φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N)))`.

Introduce `z hz`. Conclude with `(GlobalTheory.fn_hasSum_reindex_nat Ω ε h N n₀ a z (φ z) hN hcoef hzero).1 (hS z hz)`. Use `set t0 : ℝ := max C 0 + 1 with ht0`. Use `set z0 : ℂ := (t0 : ℂ) * Complex.I with hz0`. Establish `hz0im : C < z0.im`.

Simplify using `[z0, t0]`. Use `le_max_left C 0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `set x0 : ℂ := Complex.exp (2 * Real.pi * Complex.I * z0 / N) with hx0`. Establish `hx0pos : 0 < ‖x0‖` using `norm_pos_iff.2 (Complex.exp_ne_zero _)`.

Establish `hsum0` using `hred z0 hz0im`. Establish `hconv : ∀ x : ℂ, ‖x‖ < ‖x0‖ → Summable fun n => A n * x ^ n` using `fun x hx => summable_powerSeries_of_norm_lt hsum0.tendsto_sum_nat.cauchySeq hx`. Take `⟨ρ', hρ', hmain⟩` from `GlobalTheory.T.hasSum_powerSeries_inv_of_convergent A ‖x0‖ hx0pos hA0 hconv`. Establish `hmk : PowerSeries.mk A = PowerSeries.map ε p`. Use extensionality with `k`.

Simplify using `[p, A]`. Establish `hmapinv : PowerSeries.map ε q = (PowerSeries.mk A)⁻¹`. Rewrite using `[PowerSeries.eq_inv_iff_mul_eq_one]`. Rewrite using `[hmk, ← map_mul, hqdef, PowerSeries.inv_mul_cancel _ hp0, map_one]`. Simplify using `using hA0`.

Use `⟨max C ((N : ℝ) * |Real.log ρ'| / (2 * Real.pi)), fun z hz => ?_⟩` and prove the remaining obligations. Establish `hzC : C < z.im` using `lt_of_le_of_lt (le_max_left _ _) hz`. Establish `hzL : (N : ℝ) * |Real.log ρ'| / (2 * Real.pi) < z.im` using `lt_of_le_of_lt (le_max_right _ _) hz`. Use `set x : ℂ := Complex.exp (2 * Real.pi * Complex.I * z / N) with hxdef`. Establish `hx : ‖x‖ < ρ'`.

Rewrite using `[hxdef, hnorm, ← Real.exp_log hρ']`. Apply `Real.exp_lt_exp.2` to reduce the goal to its premises. Establish `hpi : 0 < 2 * Real.pi` using `by positivity`. Establish `hNr : (0 : ℝ) < N` using `by exact_mod_cast hN`. Rewrite `hzL` using `[div_lt_iff₀ hpi]`.

Establish `h1 : |Real.log ρ'| < 2 * Real.pi * z.im / N`. Rewrite using `[lt_div_iff₀ hNr]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `neg_abs_le (Real.log ρ')`. Establish `h3 : -(2 * Real.pi * z.im / N) = -(2 * Real.pi * z.im / N)` using `rfl`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hS0, hinv⟩` from `hmain x hx`. Establish `htsum : (∑' n, A n * x ^ n) = φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))` using `(hred z hzC).tsum_eq`. Rewrite using `[hg]`. Apply `(GlobalTheory.fn_hasSum_reindex_nat Ω ε g N (-n₀) (fun k => PowerSeries.coeff k q) z (φ⁻¹ z) hN hgc hgz).2` to reduce the goal to its premises.

Use `hinv using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `k`. Rewrite using `[← hmapinv, PowerSeries.coeff_map]`. Rewrite using `[htsum, mul_inv, ← Complex.exp_neg, Pi.inv_apply]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fn_hahnSeries_inv_converges : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ : ℂ → ℂ) (h : HahnSeries ℚ Ω), Den h → h ≠ 0 → HS ε C φ h → Den h⁻¹ ∧ ∃ C' : ℝ, HS ε C' φ⁻¹ h⁻¹ := by
  intro Ω _ ε C φ h hD hne hS
  obtain ⟨N, n₀, a, hN, ha0, hcoef, hzero⟩ := GlobalTheory.T.hahnSeries_commonDenominator_eq_monomial_mul_powerSeries Ω h hD hne
  obtain ⟨Φ, hΦ1, hΦ0⟩ := GlobalTheory.T.powerSeries_as_rat_hahnSeries_fractional_q Ω N hN
  set p : PowerSeries Ω := PowerSeries.mk a with hpdef
  have hp0 : PowerSeries.constantCoeff p ≠ 0 := by simpa [p] using ha0
  set q : PowerSeries Ω := p⁻¹ with hqdef
  have hdiv : ∀ (r : ℚ) (m : ℤ) (k : ℕ), r - (m : ℚ) / N = (k : ℚ) / N ↔ r = ((m + k : ℤ) : ℚ) / N := by
    intro r m k
    rw [sub_eq_iff_eq_add]
    push_cast
    constructor <;> intro hr <;> rw [hr] <;> ring
  have hh : h = HahnSeries.single ((n₀ : ℚ) / N) (1 : Ω) * Φ p := by
    ext r
    rw [HahnSeries.coeff_single_mul, one_mul]
    by_cases hr : ∃ k : ℕ, r = ((n₀ + k : ℤ) : ℚ) / N
    · obtain ⟨k, rfl⟩ := hr
      rw [hcoef k, (hdiv _ n₀ k).2 rfl, hΦ1]
      simp [p]
    · push_neg at hr
      rw [hzero r hr, hΦ0]
      intro k hk
      exact hr k ((hdiv r n₀ k).1 hk)
  set g : HahnSeries ℚ Ω := HahnSeries.single (((-n₀ : ℤ) : ℚ) / N) (1 : Ω) * Φ q with hgdef
  have hg : h⁻¹ = g := by
    symm
    apply eq_inv_of_mul_eq_one_right
    rw [hh, mul_mul_mul_comm, HahnSeries.single_mul_single, ← map_mul, hqdef,
      PowerSeries.mul_inv_cancel _ hp0, map_one, mul_one, mul_one]
    have : (n₀ : ℚ) / N + ((-n₀ : ℤ) : ℚ) / N = 0 := by push_cast; ring
    rw [this, HahnSeries.single_zero_one]
  have hgc : ∀ k : ℕ, g.coeff (((-n₀ + k : ℤ) : ℚ) / N) = PowerSeries.coeff k q := by
    intro k
    rw [hgdef, HahnSeries.coeff_single_mul, one_mul, (hdiv _ (-n₀) k).2 rfl, hΦ1]
  have hgz : ∀ r : ℚ, (∀ k : ℕ, r ≠ ((-n₀ + k : ℤ) : ℚ) / N) → g.coeff r = 0 := by
    intro r hr
    rw [hgdef, HahnSeries.coeff_single_mul, one_mul]
    apply hΦ0
    intro k hk
    exact hr k ((hdiv r (-n₀) k).1 hk)
  refine ⟨?_, ?_⟩
  · rw [hg]
    refine ⟨N, hN, fun r hr => ?_⟩
    by_contra H
    push_neg at H
    exact hr (hgz r fun k hk => H _ hk)

  set A : ℕ → ℂ := fun k => ε (a k) with hAdef
  have hA0 : A 0 ≠ 0 := (map_ne_zero ε).2 ha0
  have hnorm : ∀ z : ℂ, ‖Complex.exp (2 * Real.pi * Complex.I * z / N)‖ = Real.exp (-(2 * Real.pi * z.im / N)) := by
    intro z
    rw [Complex.norm_exp]
    congr 1
    have hNc : ((N : ℂ)) = ((N : ℝ) : ℂ) := by push_cast; rfl
    rw [hNc, Complex.div_ofReal_re]
    simp
    ring
  have hred : ∀ z : ℂ, C < z.im → HasSum (fun k : ℕ => A k * Complex.exp (2 * Real.pi * Complex.I * z / N) ^ k) (φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N))) := by
    intro z hz
    exact (GlobalTheory.fn_hasSum_reindex_nat Ω ε h N n₀ a z (φ z) hN hcoef hzero).1 (hS z hz)
  set t0 : ℝ := max C 0 + 1 with ht0
  set z0 : ℂ := (t0 : ℂ) * Complex.I with hz0
  have hz0im : C < z0.im := by
    simp [z0, t0]
    have := le_max_left C 0
    linarith
  set x0 : ℂ := Complex.exp (2 * Real.pi * Complex.I * z0 / N) with hx0
  have hx0pos : 0 < ‖x0‖ := norm_pos_iff.2 (Complex.exp_ne_zero _)
  have hsum0 := hred z0 hz0im
  have hconv : ∀ x : ℂ, ‖x‖ < ‖x0‖ → Summable fun n => A n * x ^ n := fun x hx =>
    summable_powerSeries_of_norm_lt hsum0.tendsto_sum_nat.cauchySeq hx
  obtain ⟨ρ', hρ', hmain⟩ := GlobalTheory.T.hasSum_powerSeries_inv_of_convergent A ‖x0‖ hx0pos hA0 hconv
  have hmk : PowerSeries.mk A = PowerSeries.map ε p := by
    ext k
    simp [p, A]
  have hmapinv : PowerSeries.map ε q = (PowerSeries.mk A)⁻¹ := by
    rw [PowerSeries.eq_inv_iff_mul_eq_one]
    · rw [hmk, ← map_mul, hqdef, PowerSeries.inv_mul_cancel _ hp0, map_one]
    · simpa using hA0
  refine ⟨max C ((N : ℝ) * |Real.log ρ'| / (2 * Real.pi)), fun z hz => ?_⟩
  have hzC : C < z.im := lt_of_le_of_lt (le_max_left _ _) hz
  have hzL : (N : ℝ) * |Real.log ρ'| / (2 * Real.pi) < z.im := lt_of_le_of_lt (le_max_right _ _) hz
  set x : ℂ := Complex.exp (2 * Real.pi * Complex.I * z / N) with hxdef
  have hx : ‖x‖ < ρ' := by
    rw [hxdef, hnorm, ← Real.exp_log hρ']
    apply Real.exp_lt_exp.2
    have hpi : 0 < 2 * Real.pi := by positivity
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_lt_iff₀ hpi] at hzL
    have h1 : |Real.log ρ'| < 2 * Real.pi * z.im / N := by
      rw [lt_div_iff₀ hNr]; linarith
    have h2 := neg_abs_le (Real.log ρ')
    have h3 : -(2 * Real.pi * z.im / N) = -(2 * Real.pi * z.im / N) := rfl
    linarith
  obtain ⟨hS0, hinv⟩ := hmain x hx
  have htsum : (∑' n, A n * x ^ n) = φ z * Complex.exp (-(2 * Real.pi * Complex.I * n₀ * z / N)) :=
    (hred z hzC).tsum_eq
  rw [hg]
  apply (GlobalTheory.fn_hasSum_reindex_nat Ω ε g N (-n₀) (fun k => PowerSeries.coeff k q) z (φ⁻¹ z) hN hgc hgz).2
  convert hinv using 1
  · funext k
    rw [← hmapinv, PowerSeries.coeff_map]
  · rw [htsum, mul_inv, ← Complex.exp_neg, Pi.inv_apply]
    congr 2
    push_cast
    ring

end GlobalTheory
