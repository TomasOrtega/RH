import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `N n a f rd L hN hNn ha hf hrd hL h1 h2 h3 h4`. Establish `hN' : (1 : ℝ) ≤ N` using `by exact_mod_cast hN`. Establish `hNn' : (N : ℝ) ≤ n` using `by exact_mod_cast hNn`. Establish `ha' : (1 : ℝ) ≤ a` using `by exact_mod_cast ha`. Establish `hf' : (1 : ℝ) ≤ f` using `by exact_mod_cast hf`.

Establish `hn' : (1 : ℝ) ≤ n` using `hN'.trans hNn'`. Take `⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp L` from `⟨_, rfl⟩`. Establish `hE3 : 3 ≤ E` using `by have := Real.add_one_le_exp L; linarith`. Establish `hE1 : 1 ≤ E` using `by linarith`. Establish `hE2 : Real.exp (2 * L) = E ^ 2` using `by rw [hE, ← Real.exp_nat_mul]; norm_num`.

Establish `bn : (n : ℝ) ≤ E` using `by rw [hE]; exact (Real.log_le_iff_le_exp (by linarith)).1 h4`. Establish `bf : (f : ℝ) ≤ E ^ 2` using `by rw [← hE2]; exact (Real.log_le_iff_le_exp (by linarith)).1 h2`. Establish `brd : rd ≤ E ^ 2` using `by rw [← hE2]; exact (Real.log_le_iff_le_exp (by linarith)).1 h1`. Establish `ba : (a : ℝ) ≤ E ^ 2`. Establish `: (1 + a : ℝ) ≤ E ^ 2`.

Rewrite using `[← hE2]; exact (Real.log_le_iff_le_exp (by linarith)).1 h3`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `bN : (N : ℝ) ≤ E` using `hNn'.trans bn`. Establish `b2 : (2 : ℝ) ≤ E` using `by linarith`. Establish `b2N : (2 * N + 1 : ℝ) ≤ E ^ 2` using `by nlinarith`.

Establish `bN1 : (N + 1 : ℝ) ≤ E ^ 2` using `by nlinarith`. Establish `bsq : Real.sqrt n ≤ E`. Rewrite using `[Real.sqrt_le_left (by linarith)]; nlinarith`. Establish `bf32 : (f : ℝ) ^ ((3 : ℝ) / 2) ≤ (E ^ 2) ^ 2`. Combine the equalities or inequalities in the displayed calculation.

Establish `bfact : ((N + 1).factorial : ℝ) ≤ E ^ (4 * N)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Nat.factorial_le_pow (N + 1)` after adjusting the coercions. Use `_ = (N + 1 : ℝ) ^ (N + 1) := by push_cast; rfl`. Use `_ ≤ (E ^ 2) ^ (N + 1) := by gcongr`.

Use `_ = E ^ (2 * (N + 1)) := by rw [← pow_mul]`. Use `_ ≤ E ^ (4 * N) := pow_le_pow_right₀ hE1 (by omega)`. Establish `binner : ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd) : ℝ) ≤ E ^ 17`. Combine the equalities or inequalities in the displayed calculation. Establish `hpos : (0 : ℝ) < (N : ℝ) * Real.sqrt n * ((N + 1).factorial * ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)) ^ (2 * N + 1))`.

Establish `: (0 : ℝ) < N` using `by linarith`. Establish `: (0 : ℝ) < n` using `by linarith`. Establish `: (0 : ℝ) < a` using `by linarith`. Establish `: (0 : ℝ) < f` using `by linarith`. Establish `: (0 : ℝ) < rd` using `by linarith`.

Check the signs of the components of the expression. Establish `hle : (N : ℝ) * Real.sqrt n * ((N + 1).factorial * ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)) ^ (2 * N + 1)) ≤ E ^ (140 * N)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Real.log_pow]`. Establish `hlog` using `Real.log_le_log hpos hle`.

Rewrite `hlog` using `[Real.log_pow, hE, Real.log_exp]`. Move the coercions through the operations in `at hlog`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem log_shortFamilyNumbers_le : ∀ (N n a f : ℕ) (rd L : ℝ), 1 ≤ N → N ≤ n → 1 ≤ a → 1 ≤ f → 1 ≤ rd → 2 ≤ L → Real.log rd ≤ 2 * L → Real.log f ≤ 2 * L → Real.log (1 + a) ≤ 2 * L → Real.log n ≤ L → Real.log (((N : ℝ) * Real.sqrt n * ((N + 1).factorial * ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)) ^ (2 * N + 1))) ^ a) ≤ 140 * N * L * a := by
  intro N n a f rd L hN hNn ha hf hrd hL h1 h2 h3 h4
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNn' : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hn' : (1 : ℝ) ≤ n := hN'.trans hNn'
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp L := ⟨_, rfl⟩
  have hE3 : 3 ≤ E := by have := Real.add_one_le_exp L; linarith
  have hE1 : 1 ≤ E := by linarith
  have hE2 : Real.exp (2 * L) = E ^ 2 := by rw [hE, ← Real.exp_nat_mul]; norm_num
  have bn : (n : ℝ) ≤ E := by rw [hE]; exact (Real.log_le_iff_le_exp (by linarith)).1 h4
  have bf : (f : ℝ) ≤ E ^ 2 := by rw [← hE2]; exact (Real.log_le_iff_le_exp (by linarith)).1 h2
  have brd : rd ≤ E ^ 2 := by rw [← hE2]; exact (Real.log_le_iff_le_exp (by linarith)).1 h1
  have ba : (a : ℝ) ≤ E ^ 2 := by
    have : (1 + a : ℝ) ≤ E ^ 2 := by
      rw [← hE2]; exact (Real.log_le_iff_le_exp (by linarith)).1 h3
    linarith
  have bN : (N : ℝ) ≤ E := hNn'.trans bn
  have b2 : (2 : ℝ) ≤ E := by linarith
  have b2N : (2 * N + 1 : ℝ) ≤ E ^ 2 := by nlinarith
  have bN1 : (N + 1 : ℝ) ≤ E ^ 2 := by nlinarith
  have bsq : Real.sqrt n ≤ E := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have bf32 : (f : ℝ) ^ ((3 : ℝ) / 2) ≤ (E ^ 2) ^ 2 := by
    calc (f : ℝ) ^ ((3 : ℝ) / 2) ≤ (f : ℝ) ^ ((2 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hf' (by norm_num)
      _ = (f : ℝ) ^ 2 := Real.rpow_natCast _ _
      _ ≤ (E ^ 2) ^ 2 := by gcongr
  have bfact : ((N + 1).factorial : ℝ) ≤ E ^ (4 * N) := by
    calc ((N + 1).factorial : ℝ) ≤ (((N + 1) ^ (N + 1) : ℕ) : ℝ) := by
          exact_mod_cast Nat.factorial_le_pow (N + 1)
      _ = (N + 1 : ℝ) ^ (N + 1) := by push_cast; rfl
      _ ≤ (E ^ 2) ^ (N + 1) := by gcongr
      _ = E ^ (2 * (N + 1)) := by rw [← pow_mul]
      _ ≤ E ^ (4 * N) := pow_le_pow_right₀ hE1 (by omega)
  have binner : ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd) : ℝ)
      ≤ E ^ 17 := by
    calc ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd) : ℝ)
        ≤ (E * E ^ 2 * E) * (E ^ 2 * E ^ 2) * (E * (E ^ 2) ^ 2 * E ^ 2 * E ^ 2) := by gcongr
      _ = E ^ 17 := by ring
  have hpos : (0 : ℝ) < (N : ℝ) * Real.sqrt n * ((N + 1).factorial * ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)) ^ (2 * N + 1)) := by
    have : (0 : ℝ) < N := by linarith
    have : (0 : ℝ) < n := by linarith
    have : (0 : ℝ) < a := by linarith
    have : (0 : ℝ) < f := by linarith
    have : (0 : ℝ) < rd := by linarith
    positivity
  have hle : (N : ℝ) * Real.sqrt n * ((N + 1).factorial * ((2 * f * n) * ((2 * N + 1) * a) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd)) ^ (2 * N + 1)) ≤ E ^ (140 * N) := by
    calc _ ≤ E * E * (E ^ (4 * N) * (E ^ 17) ^ (2 * N + 1)) := by gcongr
      _ = E ^ (2 + 4 * N + 17 * (2 * N + 1)) := by ring
      _ ≤ E ^ (140 * N) := pow_le_pow_right₀ hE1 (by omega)
  rw [Real.log_pow]
  have hlog := Real.log_le_log hpos hle
  rw [Real.log_pow, hE, Real.log_exp] at hlog
  push_cast at hlog
  calc _ ≤ (a : ℝ) * (140 * N * L) := by gcongr
    _ = _ := by ring

end GlobalTheory
