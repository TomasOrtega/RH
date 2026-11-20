import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeEqHarishChandraOfGap

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.DsigSize

/- English proof (translation)
Establish `hn` using `Formalism.MainNotions.nS_cast D`. Establish `h6` using `Formalism.MainNotions.six_le_n D`. Rewrite `h6`, the goal using `[← hn]`. Use `set n : ℝ := ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) with hnd`. Establish `e2 : Formalism.MainNotions.GapDS.thrE (epsSH D.R) ≤ 4 * n ^ 3` using `Formalism.MainNotions.GapDS.thrE_le (epsSH D.R) (by linarith)`.

Establish `hf : (1 : ℝ) ≤ (D.R.f : ℝ)`. Establish `hmf : D.R.m ^ 4 ≤ D.R.f` using `by unfold StandingHypotheses at hH; exact hH.2.2.1`. Establish `h2` using `D.R.two_le_m`. Establish `: 1 ≤ D.R.m ^ 4` using `Nat.one_le_pow _ _ (by omega)`. Conclude with `le_trans this hmf` after adjusting the coercions.

Establish `hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5` using `one_le_pow₀ hf`. Establish `hn19 : 4 * n ^ 3 + 2 < n ^ 19`. Establish `e3 : n ^ 19 = n ^ 3 * n ^ 16` using `by ring`. Establish `e4 : (6 : ℝ) < n ^ 16`. Establish `: (6 : ℝ) ^ 16 ≤ n ^ 16` using `pow_le_pow_left₀ (by norm_num) h6 16`.

Use the polynomial consequences of the given equalities and inequalities. Establish `e5 : 1 ≤ n ^ 3` using `one_le_pow₀ (by linarith)`. Rewrite using `[e3]`. Use the polynomial consequences of the given equalities and inequalities. Establish `e6 : n ^ 19 ≤ n ^ 19 * (D.R.f : ℝ) ^ 5` using `le_mul_of_one_le_right (by positivity) hf5`.

Establish `e7 : n ^ 19 * (D.R.f : ℝ) ^ 5 ≤ (Cl * large₂.sc.L) * (n ^ 19 * (D.R.f : ℝ) ^ 5)` using `le_mul_of_one_le_left (by positivity) hCL`. Establish `e8 : Cl * n ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L = (Cl * large₂.sc.L) * (n ^ 19 * (D.R.f : ℝ) ^ 5)` using `by ring`. Rewrite using `[e8]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem thrE_add_one_lt {D : D7} {large₂ : SizeData₂ D} {C' Cl Cg cb Cu cT CT : ℝ} (hH : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT)
    (hCL : 1 ≤ Cl * large₂.sc.L) :
    Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < Cl * (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L := by
  have hn := Formalism.MainNotions.nS_cast D
  have h6 := Formalism.MainNotions.six_le_n D
  rw [← hn] at h6 ⊢
  set n : ℝ := ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) with hnd
  have e2 : Formalism.MainNotions.GapDS.thrE (epsSH D.R) ≤ 4 * n ^ 3 := Formalism.MainNotions.GapDS.thrE_le (epsSH D.R) (by linarith)
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have hmf : D.R.m ^ 4 ≤ D.R.f := by unfold StandingHypotheses at hH; exact hH.2.2.1
    have h2 := D.R.two_le_m
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    exact_mod_cast le_trans this hmf
  have hf5 : (1 : ℝ) ≤ (D.R.f : ℝ) ^ 5 := one_le_pow₀ hf
  have hn19 : 4 * n ^ 3 + 2 < n ^ 19 := by
    have e3 : n ^ 19 = n ^ 3 * n ^ 16 := by ring
    have e4 : (6 : ℝ) < n ^ 16 := by
      have : (6 : ℝ) ^ 16 ≤ n ^ 16 := pow_le_pow_left₀ (by norm_num) h6 16
      nlinarith
    have e5 : 1 ≤ n ^ 3 := one_le_pow₀ (by linarith)
    rw [e3]; nlinarith
  have e6 : n ^ 19 ≤ n ^ 19 * (D.R.f : ℝ) ^ 5 := le_mul_of_one_le_right (by positivity) hf5
  have e7 : n ^ 19 * (D.R.f : ℝ) ^ 5 ≤ (Cl * large₂.sc.L) * (n ^ 19 * (D.R.f : ℝ) ^ 5) :=
    le_mul_of_one_le_left (by positivity) hCL
  have e8 : Cl * n ^ 19 * (D.R.f : ℝ) ^ 5 * large₂.sc.L = (Cl * large₂.sc.L) * (n ^ 19 * (D.R.f : ℝ) ^ 5) := by ring
  rw [e8]; linarith

/- English proof (translation)
Introduce `D large₂ C' Cl Cg cb Cu cT CT hT hH hCL τ`. Conclude with `GlobalTheory.dsig_eq_fdegHC_of_gap D hT τ _ (Formalism.MainNotions.BridgeLemma.szh_hc hH τ) (Formalism.MainNotions.BridgeLemma.szh_gap hH τ) (thrE_add_one_lt hH hCL)`.
-/
theorem dsigHC : Formalism.L2.SG.Pf.SzHypFD.DsigHC := by
  intro D large₂ C' Cl Cg cb Cu cT CT hT hH hCL τ
  exact GlobalTheory.dsig_eq_fdegHC_of_gap D hT τ _ (Formalism.MainNotions.BridgeLemma.szh_hc hH τ) (Formalism.MainNotions.BridgeLemma.szh_gap hH τ)
    (thrE_add_one_lt hH hCL)

end GlobalTheory.DsigSize
