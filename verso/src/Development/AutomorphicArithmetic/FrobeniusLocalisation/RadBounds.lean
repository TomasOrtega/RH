import Development.AutomorphicArithmetic.FrobeniusLocalisation.DiffDefs
import Development.AutomorphicArithmetic.FrobeniusLocalisation.LogRdSum
import Development.AutomorphicArithmetic.FrobeniusLocalisation.MemRam

open UpperTheory.HF

open NumberField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

/- English proof (translation)
Introduce `φ H`. Take `⟨hs, -, -, hrd⟩` from `UpperTheory.HF.log_rd_sum H`. Establish `hp : ∀ l ∈ H.ram, l.Prime` using `fun l hl => Nat.prime_of_mem_primeFactors hl`. Establish `hv : ∀ l ∈ H.ram, 1 / 2 ≤ H.vdH l` using `fun l hl => (UpperTheory.HF.mem_ram H (hp l hl)).2.2.2.1 hl`. Establish `hl0 : ∀ l ∈ H.ram, (0 : ℝ) < l` using `fun l hl => Nat.cast_pos.2 (hp l hl).pos`.

Establish `hlog2 : ∀ l ∈ H.ram, Real.log 2 ≤ Real.log l` using `fun l hl => Real.log_le_log (by norm_num) (by exact_mod_cast (hp l hl).two_le)`. Establish `h2 : 0 < Real.log 2` using `Real.log_pos (by norm_num)`. Establish `hlog : ∀ l ∈ H.ram, 0 ≤ Real.log l` using `fun l hl => h2.le.trans (hlog2 l hl)`. Establish `hsum : ∑ l ∈ H.ram, Real.log l ≤ 2 * Real.log H.rd`. Rewrite using `[hs, Finset.mul_sum]`.

Use `Finset.sum_le_sum fun l hl => ?_` and prove the remaining obligations. Use polynomial arithmetic with `[hv l hl, hlog l hl]`. Establish `hradpos : (0 : ℝ) < H.rad`. Unfold `HostRaw.rad`. Rewrite using `[Nat.cast_prod]`.

Conclude with `Finset.prod_pos hl0`. Establish `h1 : Real.log H.rad ≤ 2 * Real.log H.rd`. Use `le_trans (le_of_eq ?_) hsum` and prove the remaining obligations. Unfold `HostRaw.rad`. Rewrite using `[Nat.cast_prod, Real.log_prod fun l hl => (hl0 l hl).ne']`.

Use `⟨h1, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[le_div_iff₀ h2]`. Use `le_trans ?_ hsum` and prove the remaining obligations. Use `Finset.card_nsmul_le_sum H.ram (fun l : ℕ => Real.log l) _ hlog2` as an intermediate fact. Simplify using `using this`.

Introduce `D₀ hD`. Rewrite using `[hs, Finset.mul_sum]`. Use `Finset.sum_le_sum fun l hl => ?_` and prove the remaining obligations. Establish `hc : (⌈H.vdH l * D₀⌉ : ℝ) ≤ (D₀ + 2) * H.vdH l`. Use `(Int.ceil_lt_add_one (H.vdH l * D₀)).le` as an intermediate fact.

Use polynomial arithmetic with `[hv l hl]`. Rewrite using `[← mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right hc (hlog l hl)`. Establish `hpos : (0 : ℝ) < ((∏ l ∈ H.ram, l ^ ⌈H.vdH l⌉₊ : ℕ) : ℝ)`. Rewrite using `[Nat.cast_prod]`.

Conclude with `Finset.prod_pos fun l hl => by`. Rewrite using `[Nat.cast_pow]`. Conclude with `pow_pos (hl0 l hl) _`. Rewrite using `[← Real.log_le_log_iff hpos (pow_pos hrd 2), Real.log_pow, Nat.cast_prod, Real.log_prod fun l hl => by rw [Nat.cast_pow]; exact (pow_pos (hl0 l hl) _).ne', hs, Finset.mul_sum]`. Use `Finset.sum_le_sum fun l hl => ?_` and prove the remaining obligations.

Rewrite using `[Nat.cast_pow, Real.log_pow, ← mul_assoc]`. Use `mul_le_mul_of_nonneg_right ?_ (hlog l hl)` and prove the remaining obligations. Establish `hy` using `hv l hl`. Use `push_cast`. Distinguish the cases in `h : H.vdH l ≤ 1`.

Establish `: ⌈H.vdH l⌉₊ ≤ 1` using `Nat.ceil_le.2 (by simpa using h)`. Establish `: (⌈H.vdH l⌉₊ : ℝ) ≤ 1` using `by exact_mod_cast this`. Combine the linear equalities and inequalities to obtain the conclusion. Use `(Nat.ceil_lt_add_one (by linarith : 0 ≤ H.vdH l)).le push Not at h` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce `g₁ g₂ L h₁ h₂ hg₁ hg₂ hL`. Prove the components needed by the constructor for the conclusion. Rewrite using `[Real.log_mul (mul_pos h₁ h₂).ne' hradpos.ne']`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Real.log_mul h₁.ne' h₂.ne']`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.HF.rad_bounds :
    ∀ {φ : Frame} (H : HostAx φ), Real.log H.rad ≤ 2 * Real.log H.rd ∧ (H.ram.card : ℝ) ≤ 2 * Real.log H.rd / Real.log 2 ∧ (∀ D₀ : ℝ, 0 ≤ D₀ → ∑ l ∈ H.ram, (⌈H.vdH l * D₀⌉ : ℝ) * Real.log l ≤ (D₀ + 2) * Real.log H.rd) ∧ ((∏ l ∈ H.ram, l ^ ⌈H.vdH l⌉₊ : ℕ) : ℝ) ≤ H.rd ^ 2 ∧ ∀ g₁ g₂ L : ℝ, 0 < g₁ → 0 < g₂ → Real.log g₁ ≤ 9 * L + 1 → Real.log g₂ ≤ 9 * L + 1 → Real.log H.rd ≤ L / 100 → Real.log (g₁ * g₂ * H.rad) ≤ Real.log (g₁ * g₂) + 2 * Real.log H.rd ∧ Real.log (g₁ * g₂) + 2 * Real.log H.rd ≤ 18 * L + 2 + L / 50 := by
  intro φ H
  obtain ⟨hs, -, -, hrd⟩ := UpperTheory.HF.log_rd_sum H
  have hp : ∀ l ∈ H.ram, l.Prime := fun l hl => Nat.prime_of_mem_primeFactors hl
  have hv : ∀ l ∈ H.ram, 1 / 2 ≤ H.vdH l := fun l hl => (UpperTheory.HF.mem_ram H (hp l hl)).2.2.2.1 hl
  have hl0 : ∀ l ∈ H.ram, (0 : ℝ) < l := fun l hl => Nat.cast_pos.2 (hp l hl).pos
  have hlog2 : ∀ l ∈ H.ram, Real.log 2 ≤ Real.log l := fun l hl =>
    Real.log_le_log (by norm_num) (by exact_mod_cast (hp l hl).two_le)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : ∀ l ∈ H.ram, 0 ≤ Real.log l := fun l hl => h2.le.trans (hlog2 l hl)
  have hsum : ∑ l ∈ H.ram, Real.log l ≤ 2 * Real.log H.rd := by
    rw [hs, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    nlinarith [hv l hl, hlog l hl]
  have hradpos : (0 : ℝ) < H.rad := by
    unfold HostRaw.rad
    rw [Nat.cast_prod]
    exact Finset.prod_pos hl0
  have h1 : Real.log H.rad ≤ 2 * Real.log H.rd := by
    refine le_trans (le_of_eq ?_) hsum
    unfold HostRaw.rad
    rw [Nat.cast_prod, Real.log_prod fun l hl => (hl0 l hl).ne']
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ h2]
    refine le_trans ?_ hsum
    have := Finset.card_nsmul_le_sum H.ram (fun l : ℕ => Real.log l) _ hlog2
    simpa using this
  · intro D₀ hD
    rw [hs, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    have hc : (⌈H.vdH l * D₀⌉ : ℝ) ≤ (D₀ + 2) * H.vdH l := by
      have := (Int.ceil_lt_add_one (H.vdH l * D₀)).le
      nlinarith [hv l hl]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hc (hlog l hl)
  · have hpos : (0 : ℝ) < ((∏ l ∈ H.ram, l ^ ⌈H.vdH l⌉₊ : ℕ) : ℝ) := by
      rw [Nat.cast_prod]
      exact Finset.prod_pos fun l hl => by
        rw [Nat.cast_pow]; exact pow_pos (hl0 l hl) _
    rw [← Real.log_le_log_iff hpos (pow_pos hrd 2), Real.log_pow, Nat.cast_prod,
      Real.log_prod fun l hl => by rw [Nat.cast_pow]; exact (pow_pos (hl0 l hl) _).ne', hs, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    rw [Nat.cast_pow, Real.log_pow, ← mul_assoc]
    refine mul_le_mul_of_nonneg_right ?_ (hlog l hl)
    have hy := hv l hl
    push_cast
    by_cases h : H.vdH l ≤ 1
    · have : ⌈H.vdH l⌉₊ ≤ 1 := Nat.ceil_le.2 (by simpa using h)
      have : (⌈H.vdH l⌉₊ : ℝ) ≤ 1 := by exact_mod_cast this
      linarith
    · have := (Nat.ceil_lt_add_one (by linarith : 0 ≤ H.vdH l)).le
      push Not at h
      linarith
  · intro g₁ g₂ L h₁ h₂ hg₁ hg₂ hL
    constructor
    · rw [Real.log_mul (mul_pos h₁ h₂).ne' hradpos.ne']
      linarith
    · rw [Real.log_mul h₁.ne' h₂.ne']
      linarith
