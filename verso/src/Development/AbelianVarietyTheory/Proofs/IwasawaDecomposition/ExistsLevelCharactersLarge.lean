import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DuStarPos
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormPrime

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem
open scoped TensorProduct

namespace GlobalTheory.Mem.LevelPrime

/- English proof (translation)
Establish `h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ)` using `by norm_num`. Rewrite using `[Nat.cast_one, div_one, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT _), ← Real.rpow_mul hT, mul_one_div_cancel hx.ne', Real.rpow_one, h4, ← Real.rpow_mul (by norm_num), mul_right_comm, ← Real.rpow_add (by norm_num)]`. Establish `h0 : (2 : ℝ) * (1 / x) + -2 / x = 0` using `by ring`. Rewrite using `[h0, Real.rpow_zero, one_mul]`.
-/
theorem window_low {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) :
    (4 * T ^ x / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / x) * (2 : ℝ) ^ (-(2 : ℝ) / x) = T := by
  have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) := by norm_num
  rw [Nat.cast_one, div_one, Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT _), ← Real.rpow_mul hT,
    mul_one_div_cancel hx.ne', Real.rpow_one, h4, ← Real.rpow_mul (by norm_num), mul_right_comm,
    ← Real.rpow_add (by norm_num)]
  have h0 : (2 : ℝ) * (1 / x) + -2 / x = 0 := by ring
  rw [h0, Real.rpow_zero, one_mul]

/- English proof (translation)
Introduce `P N`. Establish `hq8 : P.H.q % 8 = 3` using `P.H.hyp.2.2.1`. Establish `hd16 : P.H.d % 16 = 7` using `P.H.hyp.2.2.2.1`. Establish `hn : 0 < P.R.n` using `Nat.pos_of_ne_zero (by unfold Ranks.n; positivity)`. Establish `hq : 0 < P.H.q` using `by omega`.

Establish `hd : 0 < P.H.d` using `by omega`. Establish `hQ : 0 < P.H.QS` using `P.H.QS_pos`. Establish `hg0 : 0 < P.H.g 0` using `(P.level_cond _ (P.H.g_level 0)).1.pos`. Establish `hg1 : 0 < P.H.g 1` using `(P.level_cond _ (P.H.g_level 1)).1.pos`. Establish `hc : 1 < P.H.QS * P.H.q * P.H.d`.

Establish `h1 : 0 < P.H.QS * P.H.q` using `Nat.mul_pos hQ hq`. Establish `h2 : P.H.d ≤ P.H.QS * P.H.q * P.H.d` using `Nat.le_mul_of_pos_left _ h1`. Use linear arithmetic over natural numbers and integers. Establish `hM : P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 ≠ 0` using `by positivity`. Take `⟨π, p, hp, hN, hK, hnorm, hcong, hmod⟩` from `exists_norm_prime P.R P.H _ 1 (N + P.H.pde + P.H.pde') hM (Nat.coprime_one_left _)`.

Establish `hmod' : p % (P.H.QS * P.H.q * P.H.d) = 1`. Establish `h` using `hmod.of_mul_right _`. Rewrite `h` using `[one_pow]`. Conclude with `Eq.trans h (Nat.mod_eq_of_lt hc)`. Establish `hx : (0 : ℝ) < (P.R.f : ℝ) * P.R.k`.

Establish `hf : 0 < P.R.f` using `by unfold Ranks.f; omega`. Establish `hk : 0 < P.R.k` using `by have := P.R.m_add_three_le_k; omega`. Check the signs of the components of the expression. Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hp.pos`. Use `⟨{ T := fun _ => p T_prime := fun _ => hp T_cond := fun _ => hmod' piT := fun _ => π piT_K := fun _ => hK piT_norm := fun _ => hnorm piT_cong := fun _ => by simpa only [Nat.cast_one] using hcong T_ne_pde := fun _ => ⟨by omega, by omega⟩ duStar := fun _ => 1 duStar_pos := fun _ => …` and prove the remaining obligations.

Rewrite using `[window_low hx hp0.le]`. Use `⟨le_rfl, ?_⟩` and prove the remaining obligations. Establish `h1 : (0 : ℝ) ≤ 1 / ((P.R.f : ℝ) * P.R.k)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_levCh_gt : ∀ (P : PreCh) (N : ℕ), ∃ L : LevCh P, ∀ u, N < L.T u := by
  intro P N
  have hq8 : P.H.q % 8 = 3 := P.H.hyp.2.2.1
  have hd16 : P.H.d % 16 = 7 := P.H.hyp.2.2.2.1
  have hn : 0 < P.R.n := Nat.pos_of_ne_zero (by unfold Ranks.n; positivity)
  have hq : 0 < P.H.q := by omega
  have hd : 0 < P.H.d := by omega
  have hQ : 0 < P.H.QS := P.H.QS_pos
  have hg0 : 0 < P.H.g 0 := (P.level_cond _ (P.H.g_level 0)).1.pos
  have hg1 : 0 < P.H.g 1 := (P.level_cond _ (P.H.g_level 1)).1.pos
  have hc : 1 < P.H.QS * P.H.q * P.H.d := by
    have h1 : 0 < P.H.QS * P.H.q := Nat.mul_pos hQ hq
    have h2 : P.H.d ≤ P.H.QS * P.H.q * P.H.d := Nat.le_mul_of_pos_left _ h1
    omega
  have hM : P.H.QS * P.H.q * P.H.d * (P.H.g 0 * P.H.g 1) ^ 2 ≠ 0 := by positivity
  obtain ⟨π, p, hp, hN, hK, hnorm, hcong, hmod⟩ := exists_norm_prime P.R P.H _ 1
    (N + P.H.pde + P.H.pde') hM (Nat.coprime_one_left _)
  have hmod' : p % (P.H.QS * P.H.q * P.H.d) = 1 := by
    have h := hmod.of_mul_right _
    rw [one_pow] at h
    exact Eq.trans h (Nat.mod_eq_of_lt hc)
  have hx : (0 : ℝ) < (P.R.f : ℝ) * P.R.k := by
    have hf : 0 < P.R.f := by unfold Ranks.f; omega
    have hk : 0 < P.R.k := by have := P.R.m_add_three_le_k; omega
    positivity
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  refine ⟨{ T := fun _ => p
            T_prime := fun _ => hp
            T_cond := fun _ => hmod'
            piT := fun _ => π
            piT_K := fun _ => hK
            piT_norm := fun _ => hnorm
            piT_cong := fun _ => by simpa only [Nat.cast_one] using hcong
            T_ne_pde := fun _ => ⟨by omega, by omega⟩
            duStar := fun _ => 1
            duStar_pos := fun _ => one_pos
            Dstar := 4 * (p : ℝ) ^ ((P.R.f : ℝ) * P.R.k)
            Dstar_pos := by positivity
            GamP := 2
            one_lt_gammaP := by norm_num
            T_win := fun _ => ?_ }, fun _ => by show N < p; omega⟩
  rw [window_low hx hp0.le]
  refine ⟨le_rfl, ?_⟩
  have h1 : (0 : ℝ) ≤ 1 / ((P.R.f : ℝ) * P.R.k) := by positivity
  nlinarith

end GlobalTheory.Mem.LevelPrime
