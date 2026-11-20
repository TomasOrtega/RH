import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothDetPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IndLineGL.CellCharNe

open GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[Units.val_pow_eq_pow_val, norm_pow, MonoidHom.mul_apply, Units.val_mul, norm_mul, hχ, one_mul, val_absPow_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k t).le _), ← Real.rpow_natCast, ← Real.rpow_mul (nabs_pos' k t).le, mul_comm]`.
-/
theorem norm_unitary_absPow_pow (χ : kˣ →* ℂˣ) (hχ : ∀ x, ‖((χ x : ℂˣ) : ℂ)‖ = 1) (s : ℝ) (n : ℕ) (t : kˣ) :
    ‖((((χ * absPow k (s : ℂ)) t ^ n : ℂˣ)) : ℂ)‖ = nabs k t ^ ((n : ℝ) * s) := by
  rw [Units.val_pow_eq_pow_val, norm_pow, MonoidHom.mul_apply, Units.val_mul, norm_mul, hχ, one_mul,
    val_absPow_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (nabs_pos' k t).le _),
    ← Real.rpow_natCast, ← Real.rpow_mul (nabs_pos' k t).le, mul_comm]

/- English proof (translation)
Establish `e : ∀ n : ℕ, ((1 - ((n : ℕ) : ℂ)) / 2) = (((1 - (n : ℝ)) / 2 : ℝ) : ℂ)` using `fun n => by push_cast; ring`. Simplify using `only [cellChar, Fintype.prod_bool, cond_true, cond_false, map_one, one_pow, mul_one]`. Rewrite using `[e a, e a', Units.val_mul, norm_mul, norm_unitary_absPow_pow β₀ hβ, norm_unitary_absPow_pow α₀ hα, ← Real.rpow_add (nabs_pos' k t)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_cellChar_left (a a' : ℕ) (α₀ β₀ : kˣ →* ℂˣ) (hα : ∀ x, ‖((α₀ x : ℂˣ) : ℂ)‖ = 1)
    (hβ : ∀ x, ‖((β₀ x : ℂˣ) : ℂ)‖ = 1) (b : Bool → Fin 3 → ℕ) (t : kˣ) :
    ‖((cellChar k a a' α₀ β₀ b t 1 : ℂˣ) : ℂ)‖ =
      nabs k t ^ ((b false 0 : ℝ) * ((1 - (a : ℝ)) / 2) + (b true 0 : ℝ) * ((1 - (a' : ℝ)) / 2)) := by
  have e : ∀ n : ℕ, ((1 - ((n : ℕ) : ℂ)) / 2) = (((1 - (n : ℝ)) / 2 : ℝ) : ℂ) := fun n => by push_cast; ring
  simp only [cellChar, Fintype.prod_bool, cond_true, cond_false, map_one, one_pow, mul_one]
  rw [e a, e a', Units.val_mul, norm_mul, norm_unitary_absPow_pow β₀ hβ, norm_unitary_absPow_pow α₀ hα,
    ← Real.rpow_add (nabs_pos' k t)]
  congr 1
  ring

/- English proof (translation)
Establish `e : ∀ n : ℕ, ((((n : ℕ) : ℂ) - 1) / 2) = ((((n : ℝ) - 1) / 2 : ℝ) : ℂ)` using `fun n => by push_cast; ring`. Simplify using `only [cellChar, Fintype.prod_bool, cond_true, cond_false, map_one, one_pow, one_mul]`. Rewrite using `[e a, e a', Units.val_mul, norm_mul, norm_unitary_absPow_pow β₀ hβ, norm_unitary_absPow_pow α₀ hα, ← Real.rpow_add (nabs_pos' k t)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_cellChar_right (a a' : ℕ) (α₀ β₀ : kˣ →* ℂˣ) (hα : ∀ x, ‖((α₀ x : ℂˣ) : ℂ)‖ = 1)
    (hβ : ∀ x, ‖((β₀ x : ℂˣ) : ℂ)‖ = 1) (b : Bool → Fin 3 → ℕ) (t : kˣ) :
    ‖((cellChar k a a' α₀ β₀ b 1 t : ℂˣ) : ℂ)‖ =
      nabs k t ^ ((b false 2 : ℝ) * (((a : ℝ) - 1) / 2) + (b true 2 : ℝ) * (((a' : ℝ) - 1) / 2)) := by
  have e : ∀ n : ℕ, ((((n : ℕ) : ℂ) - 1) / 2) = ((((n : ℝ) - 1) / 2 : ℝ) : ℂ) := fun n => by push_cast; ring
  simp only [cellChar, Fintype.prod_bool, cond_true, cond_false, map_one, one_pow, one_mul]
  rw [e a, e a', Units.val_mul, norm_mul, norm_unitary_absPow_pow β₀ hβ, norm_unitary_absPow_pow α₀ hα,
    ← Real.rpow_add (nabs_pos' k t)]
  congr 1
  ring

/- English proof (translation)
Take `⟨hr, hc⟩` from `b.2`. Establish `c0` using `hc 0`. Establish `c1` using `hc 1`. Establish `c2` using `hc 2`. Establish `r0` using `hr false`.

Establish `r1` using `hr true`. Establish `ea : Fintype.card (Two (Fin a) (Fin a') false) = a` using `Fintype.card_fin a`. Establish `ea' : Fintype.card (Two (Fin a) (Fin a') true) = a'` using `Fintype.card_fin a'`. Simplify using `only [Fintype.sum_bool, Fin.sum_univ_three, Fintype.card_fin, ea, ea'] at c0 c1 c2 r0 r1`. Simplify using `at c0 c1 c2`.

Use linear arithmetic over natural numbers and integers.
-/
theorem sums {a a' m : ℕ} (b : SizeMatrix (Two (Fin a) (Fin a')) (fun j : Fin 3 => Fin (blk3 m j))) :
    b.1 false 0 + b.1 true 0 = 1 ∧ b.1 false 1 + b.1 true 1 = m ∧ b.1 false 2 + b.1 true 2 = 1 ∧
      b.1 false 0 + b.1 false 1 + b.1 false 2 = a ∧ b.1 true 0 + b.1 true 1 + b.1 true 2 = a' := by
  obtain ⟨hr, hc⟩ := b.2
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  have r0 := hr false
  have r1 := hr true
  have ea : Fintype.card (Two (Fin a) (Fin a') false) = a := Fintype.card_fin a
  have ea' : Fintype.card (Two (Fin a) (Fin a') true) = a' := Fintype.card_fin a'
  simp only [Fintype.sum_bool, Fin.sum_univ_three, Fintype.card_fin, ea, ea'] at c0 c1 c2 r0 r1
  simp at c0 c1 c2
  omega

end GlobalTheory.IndLineGL.CellCharNe

namespace GlobalTheory.IndLineGL.CellCharNe

open GlobalTheory.SplitWeil

/- English proof (translation)
Use `congrArg Real.log h` as an intermediate fact. Rewrite `this` using `[Real.log_rpow h0, Real.log_rpow h0]`. Conclude with `mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one h0 h1.ne) this`.
-/
theorem rpow_exp_eq {x p q : ℝ} (h0 : 0 < x) (h1 : x < 1) (h : x ^ p = x ^ q) : p = q := by
  have := congrArg Real.log h
  rw [Real.log_rpow h0, Real.log_rpow h0] at this
  exact mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one h0 h1.ne) this

/- English proof (translation)
Introduce `k _ _ _ _ a a' m α₀ β₀ hα hβ hlt b b' hne`. Take `⟨z, -, hz⟩` from `GlobalTheory.CentralExponent.exists_nabs_lt_one k`. Establish `hz0` using `nabs_pos' k z`. Establish `haa : ((a' : ℝ) - a) ≠ 0`. Establish `: (a' : ℝ) < a` using `by exact_mod_cast hlt`.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨s0, s1, s2, -, -⟩` from `sums b`. Take `⟨s0', s1', s2', -, -⟩` from `sums b'`. Take `⟨-, -, -, ra, ra'⟩` from `sums b`. Take `⟨-, -, -, rb, rb'⟩` from `sums b'`.

Distinguish the cases in `h0 : b.1 false 0 = b'.1 false 0`. Distinguish the cases in `h2 : b.1 false 2 = b'.1 false 2`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `r j`. Apply the tactic sequence `cases r <;> fin_cases j <;> simp <;> omega`. Use `⟨1, z, fun heq => h2 ?_⟩` and prove the remaining obligations. Establish `hn` using `congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) heq`. Simplify using `only at hn`.

Rewrite `hn` using `[norm_cellChar_right a a' α₀ β₀ hα hβ, norm_cellChar_right a a' α₀ β₀ hα hβ]`. Establish `E` using `rpow_exp_eq hz0 hz hn`. Establish `hs : ((b.1 false 2 : ℝ) + b.1 true 2) = 1` using `by exact_mod_cast s2`. Establish `hs' : ((b'.1 false 2 : ℝ) + b'.1 true 2) = 1` using `by exact_mod_cast s2'`. Establish `key : (((b.1 false 2 : ℝ)) - b'.1 false 2) * ((a' : ℝ) - a) = 0`.

Take the linear combination `(-2) * E + (a' - 1 : ℝ) * hs - (a' - 1 : ℝ) * hs'`. Break down `mul_eq_zero.1 key with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h` after adjusting the coercions. Conclude with `absurd h haa`. Use `⟨z, 1, fun heq => h0 ?_⟩` and prove the remaining obligations.

Establish `hn` using `congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) heq`. Simplify using `only at hn`. Rewrite `hn` using `[norm_cellChar_left a a' α₀ β₀ hα hβ, norm_cellChar_left a a' α₀ β₀ hα hβ]`. Establish `E` using `rpow_exp_eq hz0 hz hn`. Establish `hs : ((b.1 false 0 : ℝ) + b.1 true 0) = 1` using `by exact_mod_cast s0`.

Establish `hs' : ((b'.1 false 0 : ℝ) + b'.1 true 0) = 1` using `by exact_mod_cast s0'`. Establish `key : (((b.1 false 0 : ℝ)) - b'.1 false 0) * ((a' : ℝ) - a) = 0`. Take the linear combination `2 * E - (1 - a' : ℝ) * hs + (1 - a' : ℝ) * hs'`. Break down `mul_eq_zero.1 key with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h` after adjusting the coercions.

Conclude with `absurd h haa`.
-/
theorem cellChar_ne_of_ne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (a a' m : ℕ) (α₀ β₀ : kˣ →* ℂˣ), (∀ x, ‖((α₀ x : ℂˣ) : ℂ)‖ = 1) → (∀ x, ‖((β₀ x : ℂˣ) : ℂ)‖ = 1) → a' < a →
    ∀ b b' : SizeMatrix (Two (Fin a) (Fin a')) (fun j : Fin 3 => Fin (blk3 m j)), b ≠ b' →
      ∃ t₁ t₂ : kˣ, cellChar k a a' α₀ β₀ b.1 t₁ t₂ ≠ cellChar k a a' α₀ β₀ b'.1 t₁ t₂ := by
  intro k _ _ _ _ a a' m α₀ β₀ hα hβ hlt b b' hne
  obtain ⟨z, -, hz⟩ := GlobalTheory.CentralExponent.exists_nabs_lt_one k
  have hz0 := nabs_pos' k z
  have haa : ((a' : ℝ) - a) ≠ 0 := by
    have : (a' : ℝ) < a := by exact_mod_cast hlt
    linarith
  obtain ⟨s0, s1, s2, -, -⟩ := sums b
  obtain ⟨s0', s1', s2', -, -⟩ := sums b'
  obtain ⟨-, -, -, ra, ra'⟩ := sums b
  obtain ⟨-, -, -, rb, rb'⟩ := sums b'
  by_cases h0 : b.1 false 0 = b'.1 false 0
  · by_cases h2 : b.1 false 2 = b'.1 false 2
    · exfalso
      apply hne
      apply Subtype.ext
      funext r j
      cases r <;> fin_cases j <;> simp <;> omega
    · refine ⟨1, z, fun heq => h2 ?_⟩
      have hn := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) heq
      simp only at hn
      rw [norm_cellChar_right a a' α₀ β₀ hα hβ, norm_cellChar_right a a' α₀ β₀ hα hβ] at hn
      have E := rpow_exp_eq hz0 hz hn
      have hs : ((b.1 false 2 : ℝ) + b.1 true 2) = 1 := by exact_mod_cast s2
      have hs' : ((b'.1 false 2 : ℝ) + b'.1 true 2) = 1 := by exact_mod_cast s2'
      have key : (((b.1 false 2 : ℝ)) - b'.1 false 2) * ((a' : ℝ) - a) = 0 := by
        linear_combination (-2) * E + (a' - 1 : ℝ) * hs - (a' - 1 : ℝ) * hs'
      rcases mul_eq_zero.1 key with h | h
      · exact_mod_cast sub_eq_zero.1 h
      · exact absurd h haa
  · refine ⟨z, 1, fun heq => h0 ?_⟩
    have hn := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) heq
    simp only at hn
    rw [norm_cellChar_left a a' α₀ β₀ hα hβ, norm_cellChar_left a a' α₀ β₀ hα hβ] at hn
    have E := rpow_exp_eq hz0 hz hn
    have hs : ((b.1 false 0 : ℝ) + b.1 true 0) = 1 := by exact_mod_cast s0
    have hs' : ((b'.1 false 0 : ℝ) + b'.1 true 0) = 1 := by exact_mod_cast s0'
    have key : (((b.1 false 0 : ℝ)) - b'.1 false 0) * ((a' : ℝ) - a) = 0 := by
      linear_combination 2 * E - (1 - a' : ℝ) * hs + (1 - a' : ℝ) * hs'
    rcases mul_eq_zero.1 key with h | h
    · exact_mod_cast sub_eq_zero.1 h
    · exact absurd h haa

end GlobalTheory.IndLineGL.CellCharNe
