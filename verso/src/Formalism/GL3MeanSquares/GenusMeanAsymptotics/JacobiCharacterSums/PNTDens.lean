import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.SecondBlockCount
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ZeroCountFirst
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensSpace

open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h.1 hc h.2`.
-/
theorem re_lt_one_of_isLZero {M : ℕ} [NeZero M] {χ : DirichletCharacter ℂ M} {s : ℂ}
    (h : IsLZero χ s) : s.re < 1 := by
  by_contra hc
  push Not at hc
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h.1 hc h.2

/- English proof (translation)
Take `⟨C0, q0, h0⟩` from `zero_count_first`. Take `⟨C1, q1, h1⟩` from `zero_count_second`. Use `⟨24, 10, |C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ), ?_⟩` and prove the remaining obligations. Introduce `M _ T σ S hM hT hσ hS hsp`. It suffices to establish `key : (S.card : ℝ) ≤ (|C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ)) * ((M * T : ℝ) ^ (24 * (1 - σ)) * Real.log (M * T) ^ (10 : ℕ)) by`.

Establish `hpow : Real.log (M * T) ^ (10 : ℝ) = Real.log (M * T) ^ (10 : ℕ)`. Rewrite using `[← Real.rpow_natCast]`. Evaluate the numerical expressions. Rewrite using `[hpow, mul_assoc]`. Conclude with `key`.

Establish `hM' : (3 : ℝ) ≤ M` using `by exact_mod_cast hM`. Establish `hX : (6 : ℝ) ≤ M * T` using `by nlinarith`. Establish `hX0 : (0 : ℝ) < M * T` using `by linarith`. Establish `hL : (1 : ℝ) ≤ Real.log (M * T)`. Rewrite using `[Real.le_log_iff_exp_le hX0]`.

Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL10 : (1 : ℝ) ≤ Real.log (M * T) ^ 10` using `one_le_pow₀ hL`. Establish `hq0 : (0 : ℝ) ≤ ((max q0 q1 : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `hCnn : 0 ≤ |C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ)` using `by positivity`.

Establish `htriv : (S.card : ℝ) ≤ 3 * (M * T)`. Establish `h` using `trivial_bound M T S (by linarith) (fun p hp => (hS p hp).2.1) hsp`. Establish `hMnn : (0 : ℝ) ≤ M` using `by linarith`. Use the polynomial consequences of the given equalities and inequalities. Break down `S.eq_empty_or_nonempty with hE | ⟨p0, hp0⟩` into its components or cases.

Rewrite using `[hE]`. Simplify using `only [Finset.card_empty, Nat.cast_zero]`. Conclude with `mul_nonneg hCnn (mul_nonneg (Real.rpow_nonneg hX0.le _) (by positivity))`. Establish `hσ1 : σ ≤ 1`. Establish `h1'` using `re_lt_one_of_isLZero (hS p0 hp0).2.2`.

Combine the linear relations using `[(hS p0 hp0).1]`. Establish `hR1 : (1 : ℝ) ≤ (M * T) ^ (24 * (1 - σ))` using `Real.one_le_rpow (by linarith) (by linarith)`. Establish `hP : (1 : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10` using `by nlinarith`. Establish `hXP : σ < 3 / 4 → (M * T : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10`. Introduce `hs`.

Establish `hXe : (M * T : ℝ) ≤ (M * T) ^ (24 * (1 - σ))`. Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities. Establish `h0'` using `fun S hσ' hq => h0 M T σ S hM hT hσ' hq`. Establish `h1'` using `fun S hσ' hq => h1 M T σ S hM hT hσ' hq`.

Simplify using `only [mul_assoc] at h0' h1'`. Use `set P := (M * T : ℝ) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 with hPdef`. Establish `hP0 : (0 : ℝ) ≤ P` using `by linarith`. Use `set q : ℝ := ((max q0 q1 : ℕ) : ℝ) with hqdef`. Establish `hexp : (|C0| + |C1| + 3 + 3 * q) * P = |C0| * P + |C1| * P + 3 * P + 3 * q * P` using `by ring`.

Rewrite using `[hexp]`. Establish `eC0` using `mul_le_mul_of_nonneg_right (le_abs_self C0) hP0`. Establish `eC1` using `mul_le_mul_of_nonneg_right (le_abs_self C1) hP0`. Establish `a0 : 0 ≤ |C0| * P` using `mul_nonneg (abs_nonneg _) hP0`. Establish `a1 : 0 ≤ |C1| * P` using `mul_nonneg (abs_nonneg _) hP0`.

Establish `aq : q ≤ q * P` using `by nlinarith`. Distinguish the cases in `hq : max q0 q1 ≤ qd M T`. Distinguish the cases in `hσ34 : 3 / 4 ≤ σ`. Establish `hA0` using `h0' (S.filter (fun p => p.1 = 1)) hσ34 (le_trans (le_max_left _ _) hq) (by`. Introduce `p hp`.

Rewrite `hp` using `[Finset.mem_filter]`. Establish `hs` using `hS p hp.1`. Conclude with `⟨hp.2, hs.1, re_lt_one_of_isLZero hs.2.2, hs.2.1, hs.2.2⟩)`. Use the proof step `(by`. Introduce `p hp p' hp' hne`.

Rewrite `hp`, `hp'` using `[Finset.mem_filter]`. Conclude with `hsp p hp.1 p' hp'.1 hne (hp.2.trans hp'.2.symm))`. Establish `hA1` using `h1' (S.filter (fun p => ¬ p.1 = 1)) hσ34 (le_trans (le_max_right _ _) hq) (by`. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_filter]`.

Establish `hs` using `hS p hp.1`. Conclude with `⟨hp.2, hs.1, re_lt_one_of_isLZero hs.2.2, hs.2.1, hs.2.2.2⟩)`. Use the proof step `(by`. Introduce `p hp p' hp' hne heq`. Rewrite `hp`, `hp'` using `[Finset.mem_filter]`.

Conclude with `hsp p hp.1 p' hp'.1 hne heq)`. Establish `hcast : (S.card : ℝ) = ((S.filter (fun p => p.1 = 1)).card : ℝ) + ((S.filter (fun p => ¬ p.1 = 1)).card : ℝ)`. Rewrite using `[← Nat.cast_add, Finset.card_filter_add_card_filter_not]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at hσ34`.

Use `hXP hσ34` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `push_neg at hq`. Establish `hXq : (M * T : ℝ) < q`. Use `lt_of_le_of_lt (Nat.le_ceil _) ?_` and prove the remaining obligations.

Rewrite using `[hqdef]`. Unfold `qd at hq`. Conclude with `hq` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem log_density_bound : Formalism.HermitianLattices.Ext.PrimesInProgressions.LogDensityM := by
  classical
  obtain ⟨C0, q0, h0⟩ := zero_count_first
  obtain ⟨C1, q1, h1⟩ := zero_count_second
  refine ⟨24, 10, |C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ), ?_⟩
  intro M _ T σ S hM hT hσ hS hsp
  suffices key : (S.card : ℝ) ≤ (|C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ)) *
      ((M * T : ℝ) ^ (24 * (1 - σ)) * Real.log (M * T) ^ (10 : ℕ)) by
    have hpow : Real.log (M * T) ^ (10 : ℝ) = Real.log (M * T) ^ (10 : ℕ) := by
      rw [← Real.rpow_natCast]
      norm_num
    rw [hpow, mul_assoc]
    exact key
  have hM' : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hX : (6 : ℝ) ≤ M * T := by nlinarith
  have hX0 : (0 : ℝ) < M * T := by linarith
  have hL : (1 : ℝ) ≤ Real.log (M * T) := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  have hL10 : (1 : ℝ) ≤ Real.log (M * T) ^ 10 := one_le_pow₀ hL
  have hq0 : (0 : ℝ) ≤ ((max q0 q1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hCnn : 0 ≤ |C0| + |C1| + 3 + 3 * ((max q0 q1 : ℕ) : ℝ) := by positivity
  have htriv : (S.card : ℝ) ≤ 3 * (M * T) := by
    have h := trivial_bound M T S (by linarith) (fun p hp => (hS p hp).2.1) hsp
    have hMnn : (0 : ℝ) ≤ M := by linarith
    nlinarith
  rcases S.eq_empty_or_nonempty with hE | ⟨p0, hp0⟩
  · rw [hE]
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hCnn (mul_nonneg (Real.rpow_nonneg hX0.le _) (by positivity))
  have hσ1 : σ ≤ 1 := by
    have h1' := re_lt_one_of_isLZero (hS p0 hp0).2.2
    linarith [(hS p0 hp0).1]
  have hR1 : (1 : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) := Real.one_le_rpow (by linarith) (by linarith)
  have hP : (1 : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 := by nlinarith
  have hXP : σ < 3 / 4 → (M * T : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 := by
    intro hs
    have hXe : (M * T : ℝ) ≤ (M * T) ^ (24 * (1 - σ)) := by
      calc (M * T : ℝ) = (M * T) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    nlinarith
  have h0' := fun S hσ' hq => h0 M T σ S hM hT hσ' hq
  have h1' := fun S hσ' hq => h1 M T σ S hM hT hσ' hq
  simp only [mul_assoc] at h0' h1'
  set P := (M * T : ℝ) ^ (24 * (1 - σ)) * Real.log (M * T) ^ 10 with hPdef
  have hP0 : (0 : ℝ) ≤ P := by linarith
  set q : ℝ := ((max q0 q1 : ℕ) : ℝ) with hqdef
  have hexp : (|C0| + |C1| + 3 + 3 * q) * P = |C0| * P + |C1| * P + 3 * P + 3 * q * P := by ring
  rw [hexp]
  have eC0 := mul_le_mul_of_nonneg_right (le_abs_self C0) hP0
  have eC1 := mul_le_mul_of_nonneg_right (le_abs_self C1) hP0
  have a0 : 0 ≤ |C0| * P := mul_nonneg (abs_nonneg _) hP0
  have a1 : 0 ≤ |C1| * P := mul_nonneg (abs_nonneg _) hP0
  have aq : q ≤ q * P := by nlinarith
  by_cases hq : max q0 q1 ≤ qd M T
  · by_cases hσ34 : 3 / 4 ≤ σ
    · have hA0 := h0' (S.filter (fun p => p.1 = 1)) hσ34 (le_trans (le_max_left _ _) hq)
        (by
          intro p hp
          rw [Finset.mem_filter] at hp
          have hs := hS p hp.1
          exact ⟨hp.2, hs.1, re_lt_one_of_isLZero hs.2.2, hs.2.1, hs.2.2⟩)
        (by
          intro p hp p' hp' hne
          rw [Finset.mem_filter] at hp hp'
          exact hsp p hp.1 p' hp'.1 hne (hp.2.trans hp'.2.symm))
      have hA1 := h1' (S.filter (fun p => ¬ p.1 = 1)) hσ34 (le_trans (le_max_right _ _) hq)
        (by
          intro p hp
          rw [Finset.mem_filter] at hp
          have hs := hS p hp.1
          exact ⟨hp.2, hs.1, re_lt_one_of_isLZero hs.2.2, hs.2.1, hs.2.2.2⟩)
        (by
          intro p hp p' hp' hne heq
          rw [Finset.mem_filter] at hp hp'
          exact hsp p hp.1 p' hp'.1 hne heq)
      have hcast : (S.card : ℝ) = ((S.filter (fun p => p.1 = 1)).card : ℝ) +
          ((S.filter (fun p => ¬ p.1 = 1)).card : ℝ) := by
        rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]
      linarith
    · push_neg at hσ34
      have := hXP hσ34
      linarith
  · push_neg at hq
    have hXq : (M * T : ℝ) < q := by
      refine lt_of_le_of_lt (Nat.le_ceil _) ?_
      rw [hqdef]
      unfold qd at hq
      exact_mod_cast hq
    linarith

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
