import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusThreeBlockApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent GlobalTheory.IndJacBlock GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.IndJacBlock

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Unfold `chi2`. Use `split_ifs`. Simplify using the standard rewrite rules. Rewrite using `[MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hν x, inv_one]`.
-/
theorem norm_chi2_eq_one {ν : kˣ →* ℂˣ} (hν : IsUnitaryChar ν) (i : Fin 2) (x : kˣ) :
    ‖((chi2 k ν i x : ℂˣ) : ℂ)‖ = 1 := by
  unfold chi2
  split_ifs
  · simp
  · rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, norm_inv, hν x, inv_one]

/- English proof (translation)
Rewrite using `[val_absPow, Complex.norm_cpow_eq_rpow_re_of_pos (nabs_pos' k x)]`.
-/
theorem norm_absPow (s : ℂ) (x : kˣ) : ‖((absPow k s x : ℂˣ) : ℂ)‖ = nabs k x ^ s.re := by
  rw [val_absPow, Complex.norm_cpow_eq_rpow_re_of_pos (nabs_pos' k x)]

/- English proof (translation)
Simplify using `[b2]`. Use linear arithmetic over natural numbers and integers.
-/
theorem b2_ne {n d : ℕ} (h : 2 * n ≠ d) : b2 n d 0 ≠ b2 n d 1 := by
  simp [b2]; omega

/- English proof (translation)
Rewrite using `[Ne, Nat.cast_inj]`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `absurd rfl hij`. Conclude with `b2_ne h`. Conclude with `fun e => b2_ne h e.symm`.

Conclude with `absurd rfl hij`.
-/
theorem b2_injective {n d : ℕ} (h : 2 * n ≠ d) {i j : Fin 2} (hij : i ≠ j) :
    (b2 n d i : ℝ) ≠ (b2 n d j : ℝ) := by
  rw [Ne, Nat.cast_inj]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact b2_ne h
  · exact fun e => b2_ne h e.symm
  · exact absurd rfl hij

/- English proof (translation)
Establish `hl : Real.log b ≠ 0` using `(Real.log_neg hb0 hb1).ne`. Use `congrArg Real.log h` as an intermediate fact. Rewrite `this` using `[Real.log_rpow hb0, Real.log_rpow hb0]`. Conclude with `mul_right_cancel₀ hl this`.
-/
theorem rpow_exp_inj {b x y : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (h : b ^ x = b ^ y) : x = y := by
  have hl : Real.log b ≠ 0 := (Real.log_neg hb0 hb1).ne
  have := congrArg Real.log h
  rw [Real.log_rpow hb0, Real.log_rpow hb0] at this
  exact mul_right_cancel₀ hl this

/- English proof (translation)
Introduce `k _ _ _ _ n d ν hnd hν i i' j j' hij`. Take `⟨ϖ, -, hϖ⟩` from `GlobalTheory.CentralExponent.exists_nabs_lt_one k`. Establish `hp` using `nabs_pos' k ϖ`. Establish `h1 : nabs k 1 = 1` using `by simp [nabs]`. Establish `key : ∀ (a a' : Fin 2) (p : kˣ × kˣ), ‖cellChar₂ k (b2 n d) (chi2 k ν) a a' p‖ = nabs k p.1 ^ ((1 - (b2 n d a : ℝ)) / 2) * nabs k p.2 ^ (((b2 n d a' : ℝ) - 1) / 2)`.

Introduce `a a' p`. Unfold `cellChar₂`. Simplify using `only [Units.val_mul, norm_mul, norm_chi2_eq_one hν, norm_absPow, one_mul, mul_one]`. Apply the tactic sequence `congr 2 <;> simp [Complex.div_re]`. Break down `hij with h | h` into its components or cases.

Use `⟨(ϖ, 1), fun e => ?_⟩` and prove the remaining obligations. Establish `e'` using `congrArg norm e`. Rewrite `e'` using `[key, key]`. Simplify using `only [h1, Real.one_rpow, mul_one] at e'`. Use `rpow_exp_inj hp hϖ e'` as an intermediate fact.

Conclude with `b2_injective hnd h (by linarith)`. Use `⟨(1, ϖ), fun e => ?_⟩` and prove the remaining obligations. Establish `e'` using `congrArg norm e`. Rewrite `e'` using `[key, key]`. Simplify using `only [h1, Real.one_rpow, one_mul] at e'`.

Use `rpow_exp_inj hp hϖ e'` as an intermediate fact. Conclude with `b2_injective hnd h (by linarith)`.
-/
theorem cellChar_distinct : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), 2 * n ≠ d → IsUnitaryChar ν → ∀ i i' j j' : Fin 2, (i ≠ j ∨ i' ≠ j') →
    ∃ p : kˣ × kˣ, cellChar₂ k (b2 n d) (chi2 k ν) i i' p ≠ cellChar₂ k (b2 n d) (chi2 k ν) j j' p := by
  intro k _ _ _ _ n d ν hnd hν i i' j j' hij
  obtain ⟨ϖ, -, hϖ⟩ := GlobalTheory.CentralExponent.exists_nabs_lt_one k
  have hp := nabs_pos' k ϖ
  have h1 : nabs k 1 = 1 := by simp [nabs]
  have key : ∀ (a a' : Fin 2) (p : kˣ × kˣ), ‖cellChar₂ k (b2 n d) (chi2 k ν) a a' p‖ =
      nabs k p.1 ^ ((1 - (b2 n d a : ℝ)) / 2) * nabs k p.2 ^ (((b2 n d a' : ℝ) - 1) / 2) := by
    intro a a' p
    unfold cellChar₂
    simp only [Units.val_mul, norm_mul, norm_chi2_eq_one hν, norm_absPow, one_mul, mul_one]
    congr 2 <;> simp [Complex.div_re]
  rcases hij with h | h
  · refine ⟨(ϖ, 1), fun e => ?_⟩
    have e' := congrArg norm e
    rw [key, key] at e'
    simp only [h1, Real.one_rpow, mul_one] at e'
    have := rpow_exp_inj hp hϖ e'
    exact b2_injective hnd h (by linarith)
  · refine ⟨(1, ϖ), fun e => ?_⟩
    have e' := congrArg norm e
    rw [key, key] at e'
    simp only [h1, Real.one_rpow, one_mul] at e'
    have := rpow_exp_inj hp hϖ e'
    exact b2_injective hnd h (by linarith)

end GlobalTheory.IndJacBlock
