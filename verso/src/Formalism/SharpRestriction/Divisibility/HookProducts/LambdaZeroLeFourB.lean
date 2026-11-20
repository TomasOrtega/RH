import Mathlib
import Formalism.SharpRestriction.ElevenLe
import Formalism.SharpRestriction.Divisibility.SlopeExcess.FamilyStatementOfScaledLemmas

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.FunSharp

open Formalism.BasicNotions Formalism.MainNotions

/- English proof (translation)
Take `⟨-, -, hK, hKR, hT, -, -, -, -, -, -, -, -, hEta, hNodes, -, -, -, -, -, hG, -, -⟩` from `hS`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hθ : 0 ≤ szTh L` using `by unfold szTh; have := L.sc.eps_pos; positivity`. Establish `hxθ : 1 ≤ L.sc.x ^ szTh L` using `Real.one_le_rpow hx1.le hθ`. Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le`.

Establish `hb0 : 0 ≤ L.sc.b` using `by unfold Scale.b; exact (Real.exp_pos _).le`. Use `set A : ℝ := L.sc.x ^ szTh L * L.sc.L with hA`. Establish `hA1 : 1 ≤ A` using `by rw [hA]; nlinarith`. Use `set F : ℝ := (D.R.f : ℝ) with hFdef`. Use `set R : ℝ := (D.R.r : ℝ) with hRdef`.

Establish `hF1 : 1 ≤ F`. Establish `h12 : A ≤ F * Real.log D.R.k` using `hKR.2.2.2.2.2.2.2.2.2.2.2.1`. Assume the negation of the conclusion as `hc`. Establish `hf0 : D.R.f = 0`. Establish `: (D.R.f : ℝ) < 1` using `not_le.mp hc`.

Conclude with `Nat.lt_one_iff.mp (by exact_mod_cast this)` after adjusting the coercions. Rewrite `h12` using `[hFdef, hf0]`. Simplify using `at h12`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hR1 : 1 ≤ R`.

Establish `hfr : F ≤ R ^ 2` using `hKR.2.2.2.2.2.2.2.2.2.2.2.2.2`. Establish `hR0 : 0 ≤ R` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hT1 : 1 ≤ (D.R.t : ℝ)` using `hT.1`. Establish `hK1 : 1 ≤ (D.R.k : ℝ)`.

Establish `h` using `hK.1`. Establish `hp : 0 < L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L)` using `Real.rpow_pos_of_pos (by linarith) _`. Establish `hk0 : 0 < (D.R.k : ℝ)` using `lt_of_lt_of_le hp h`. Establish `: 0 < D.R.k` using `by exact_mod_cast hk0`. Conclude with `this` after adjusting the coercions.

Establish `hη1 : 1 ≤ L.etaSz` using `hT1.trans hEta.1`. Establish `hden : 1 ≤ (D.R.t : ℝ) ^ 3 * F * (D.R.k : ℝ) ^ 3`. Establish `h1 : 1 ≤ (D.R.t : ℝ) ^ 3` using `one_le_pow₀ hT1`. Establish `h2 : 1 ≤ (D.R.k : ℝ) ^ 3` using `one_le_pow₀ hK1`. Establish `h3 : 1 ≤ (D.R.t : ℝ) ^ 3 * F` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hηb : L.etaSz ≤ L.sc.b` using `hEta.2.1.trans (div_le_self hb0 hden)`. Establish `hηm : L.etaSz / D.R.m ≤ L.etaSz`. Break down `Nat.eq_zero_or_pos D.R.m with h | h` into its components or cases. Rewrite using `[h, Nat.cast_zero, div_zero]`.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `div_le_self (by linarith) (by exact_mod_cast h)`. Establish `hQ : L.sc.x ^ szTh L * R ^ 19 * F ^ 5 * L.sc.L ≤ L.sc.b` using `(hNodes.2.2.1.trans hηm).trans hηb`. Establish `hF5 : F ≤ F ^ 5` using `le_self_pow₀ hF1 (by norm_num)`. Establish `hR19 : R ^ 2 ≤ R ^ 19` using `pow_le_pow_right₀ hR1 (by norm_num)`.

Establish `hFR : F * R ^ 2 ≤ F ^ 5 * R ^ 19` using `mul_le_mul hF5 hR19 (by positivity) (by positivity)`. Establish `hQ' : F * R ^ 2 * A ≤ L.sc.b`. Establish `: F * R ^ 2 * A ≤ F ^ 5 * R ^ 19 * A` using `mul_le_mul_of_nonneg_right hFR (by linarith)`. Establish `e : F ^ 5 * R ^ 19 * A = L.sc.x ^ szTh L * R ^ 19 * F ^ 5 * L.sc.L` using `by rw [hA]; ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hFR0 : 0 ≤ F * R ^ 2` using `by positivity`. Establish `hFRb : F * R ^ 2 ≤ L.sc.b` using `le_trans (le_mul_of_one_le_right hFR0 hA1) hQ'`. Establish `hg0 : (0 : ℝ) < D.host.g 0` using `by exact_mod_cast (D.host.g_prime 0).pos`. Establish `hg1 : (1 : ℝ) ≤ D.host.g 0` using `by exact_mod_cast (D.host.g_prime 0).one_lt.le`. Establish `hlog0 : 0 ≤ Real.log (2 * (D.host.g 0 : ℝ))` using `Real.log_nonneg (by linarith)`.

Establish `hY : ∀ i, (D.host.g i : ℝ) ≤ 2 * (D.host.g 0 : ℝ)` using `fun i => (hG i 0).2.1`. Establish `h0` using `Formalism.MainNotions.DIV.Proofs.ScaledLatticeNorms.scaled_lattice_nonzero_holds D (D.host.g 0 : ℝ) hY`. Establish `hlog : Real.log (2 * (D.host.g 0 : ℝ)) ≤ 1 + A`. Rewrite using `[Real.log_mul (by norm_num) hg0.ne']`. Establish `h2 : Real.log 2 < 1` using `by have := Real.log_two_lt_d9; linarith`.

Establish `h3 : Real.log (D.host.g 0 : ℝ) ≤ A` using `(hG 0 0).2.2`. Combine the linear equalities and inequalities to obtain the conclusion. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lambda_zero_le_four_b {D : D7} (L : SizeData₂ D) (hS : SizesAt L) : lam0 D ≤ 4 * L.sc.b := by
  obtain ⟨-, -, hK, hKR, hT, -, -, -, -, -, -, -, -, hEta, hNodes, -, -, -, -, -, hG, -, -⟩ := hS
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hθ : 0 ≤ szTh L := by unfold szTh; have := L.sc.eps_pos; positivity
  have hxθ : 1 ≤ L.sc.x ^ szTh L := Real.one_le_rpow hx1.le hθ
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb0 : 0 ≤ L.sc.b := by unfold Scale.b; exact (Real.exp_pos _).le
  set A : ℝ := L.sc.x ^ szTh L * L.sc.L with hA
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith
  set F : ℝ := (D.R.f : ℝ) with hFdef
  set R : ℝ := (D.R.r : ℝ) with hRdef

  have hF1 : 1 ≤ F := by
    have h12 : A ≤ F * Real.log D.R.k := hKR.2.2.2.2.2.2.2.2.2.2.2.1
    by_contra hc
    have hf0 : D.R.f = 0 := by
      have : (D.R.f : ℝ) < 1 := not_le.mp hc
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    rw [hFdef, hf0] at h12
    simp at h12
    linarith

  have hR1 : 1 ≤ R := by
    have hfr : F ≤ R ^ 2 := hKR.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hR0 : 0 ≤ R := by positivity
    nlinarith

  have hT1 : 1 ≤ (D.R.t : ℝ) := hT.1
  have hK1 : 1 ≤ (D.R.k : ℝ) := by
    have h := hK.1
    have hp : 0 < L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) := Real.rpow_pos_of_pos (by linarith) _
    have hk0 : 0 < (D.R.k : ℝ) := lt_of_lt_of_le hp h
    have : 0 < D.R.k := by exact_mod_cast hk0
    exact_mod_cast this

  have hη1 : 1 ≤ L.etaSz := hT1.trans hEta.1
  have hden : 1 ≤ (D.R.t : ℝ) ^ 3 * F * (D.R.k : ℝ) ^ 3 := by
    have h1 : 1 ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ hT1
    have h2 : 1 ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hK1
    have h3 : 1 ≤ (D.R.t : ℝ) ^ 3 * F := by nlinarith
    nlinarith
  have hηb : L.etaSz ≤ L.sc.b := hEta.2.1.trans (div_le_self hb0 hden)
  have hηm : L.etaSz / D.R.m ≤ L.etaSz := by
    rcases Nat.eq_zero_or_pos D.R.m with h | h
    · rw [h, Nat.cast_zero, div_zero]; linarith
    · exact div_le_self (by linarith) (by exact_mod_cast h)
  have hQ : L.sc.x ^ szTh L * R ^ 19 * F ^ 5 * L.sc.L ≤ L.sc.b :=
    (hNodes.2.2.1.trans hηm).trans hηb

  have hF5 : F ≤ F ^ 5 := le_self_pow₀ hF1 (by norm_num)
  have hR19 : R ^ 2 ≤ R ^ 19 := pow_le_pow_right₀ hR1 (by norm_num)
  have hFR : F * R ^ 2 ≤ F ^ 5 * R ^ 19 := mul_le_mul hF5 hR19 (by positivity) (by positivity)
  have hQ' : F * R ^ 2 * A ≤ L.sc.b := by
    have : F * R ^ 2 * A ≤ F ^ 5 * R ^ 19 * A := mul_le_mul_of_nonneg_right hFR (by linarith)
    have e : F ^ 5 * R ^ 19 * A = L.sc.x ^ szTh L * R ^ 19 * F ^ 5 * L.sc.L := by rw [hA]; ring
    linarith
  have hFR0 : 0 ≤ F * R ^ 2 := by positivity
  have hFRb : F * R ^ 2 ≤ L.sc.b := le_trans (le_mul_of_one_le_right hFR0 hA1) hQ'

  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (1 : ℝ) ≤ D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).one_lt.le
  have hlog0 : 0 ≤ Real.log (2 * (D.host.g 0 : ℝ)) := Real.log_nonneg (by linarith)
  have hY : ∀ i, (D.host.g i : ℝ) ≤ 2 * (D.host.g 0 : ℝ) := fun i => (hG i 0).2.1
  have h0 := Formalism.MainNotions.DIV.Proofs.ScaledLatticeNorms.scaled_lattice_nonzero_holds D (D.host.g 0 : ℝ) hY
  have hlog : Real.log (2 * (D.host.g 0 : ℝ)) ≤ 1 + A := by
    rw [Real.log_mul (by norm_num) hg0.ne']
    have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have h3 : Real.log (D.host.g 0 : ℝ) ≤ A := (hG 0 0).2.2
    linarith
  calc lam0 D ≤ 2 * F * R ^ 2 * Real.log (2 * (D.host.g 0 : ℝ)) := h0
    _ ≤ 2 * F * R ^ 2 * (1 + A) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2 * (F * R ^ 2) + 2 * (F * R ^ 2 * A) := by ring
    _ ≤ 4 * L.sc.b := by linarith

end Formalism.MainNotions.DIV.HookProducts.FunSharp
