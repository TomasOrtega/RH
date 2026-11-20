import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DiagCLC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FinXClosed
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Rk

/- English proof (translation)
Introduce `D u Γ c hΓ hc h hD`. Unfold `SDiagAt at h`. Unfold `GlobalTheory.Core.Rk.DiagS`. Rewrite using `[GlobalTheory.Core.Rk.d0_eq]`. Use `set d : ℝ := (D.duS u : ℝ) with hd`.

Use `set E : ℝ := Real.exp (-(c * D.R.k * D.R.f * Real.log D.R.k)) with hE`. Use `set E1 : ℝ := Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k)) with hE1`. Establish `hd0 : 0 ≤ d` using `Nat.cast_nonneg _`. Establish `hΓ0 : 0 < Γ` using `lt_of_lt_of_le one_pos hΓ`. Establish `hX : 0 ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k` using `mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.log_natCast_nonneg _)`.

Establish `hEE : E1 ≤ E`. Rewrite using `[hE, hE1]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Establish `: c * ((D.R.k : ℝ) * D.R.f * Real.log D.R.k) ≤ 1 * ((D.R.k : ℝ) * D.R.f * Real.log D.R.k)` using `mul_le_mul_of_nonneg_right hc hX`. Establish `e : c * (D.R.k : ℝ) * D.R.f * Real.log D.R.k = c * ((D.R.k : ℝ) * D.R.f * Real.log D.R.k)` using `by ring`.

Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1 : (Γ + 1) * d ^ 2 / D.what₂.Dstar ≤ 2 * d / Γ`. Break down `hd0.eq_or_lt with h0 | h0` into its components or cases. Rewrite using `[← h0]`.

Simplify using the standard rewrite rules. Establish `hDp : 0 < D.what₂.Dstar` using `lt_of_lt_of_le (by positivity) hD`. Rewrite using `[div_le_div_iff₀ hDp hΓ0]`. Establish `: (Γ + 1) * d ^ 2 * Γ ≤ 2 * d * (d * Γ ^ 2)` using `by nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) hΓ0]`. Combine the equalities or inequalities in the displayed calculation.

Establish `h2 : 2 * d * E1 ≤ 2 * d * E` using `by apply mul_le_mul_of_nonneg_left hEE; positivity`. Establish `e3 : (8 / Γ + 6 * E) * d = 4 * (2 * d / Γ + d * E) + 2 * d * E` using `by field_simp; ring`. Rewrite using `[e3]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem diagS_of_sDiagAt : ∀ (D : D7) (u : D.what₂.Word) (Γ c : ℝ), 1 ≤ Γ → c ≤ 1 → SDiagAt D u Γ c →
    (D.duS u : ℝ) * Γ ^ 2 ≤ D.what₂.Dstar →
    GlobalTheory.Core.Rk.DiagS D u (8 / Γ + 6 * Real.exp (-(c * D.R.k * D.R.f * Real.log D.R.k))) := by
  intro D u Γ c hΓ hc h hD
  unfold SDiagAt at h
  unfold GlobalTheory.Core.Rk.DiagS
  rw [GlobalTheory.Core.Rk.d0_eq]
  set d : ℝ := (D.duS u : ℝ) with hd
  set E : ℝ := Real.exp (-(c * D.R.k * D.R.f * Real.log D.R.k)) with hE
  set E1 : ℝ := Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k)) with hE1
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hΓ0 : 0 < Γ := lt_of_lt_of_le one_pos hΓ
  have hX : 0 ≤ (D.R.k : ℝ) * D.R.f * Real.log D.R.k :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.log_natCast_nonneg _)
  have hEE : E1 ≤ E := by
    rw [hE, hE1]
    apply Real.exp_le_exp.mpr
    have : c * ((D.R.k : ℝ) * D.R.f * Real.log D.R.k) ≤ 1 * ((D.R.k : ℝ) * D.R.f * Real.log D.R.k) :=
      mul_le_mul_of_nonneg_right hc hX
    have e : c * (D.R.k : ℝ) * D.R.f * Real.log D.R.k = c * ((D.R.k : ℝ) * D.R.f * Real.log D.R.k) := by ring
    rw [e]; linarith
  have h1 : (Γ + 1) * d ^ 2 / D.what₂.Dstar ≤ 2 * d / Γ := by
    rcases hd0.eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · have hDp : 0 < D.what₂.Dstar := lt_of_lt_of_le (by positivity) hD
      rw [div_le_div_iff₀ hDp hΓ0]
      have : (Γ + 1) * d ^ 2 * Γ ≤ 2 * d * (d * Γ ^ 2) := by nlinarith [mul_pos h0 h0, mul_pos (mul_pos h0 h0) hΓ0]
      calc (Γ + 1) * d ^ 2 * Γ ≤ 2 * d * (d * Γ ^ 2) := this
        _ ≤ 2 * d * D.what₂.Dstar := by apply mul_le_mul_of_nonneg_left hD; positivity
  have h2 : 2 * d * E1 ≤ 2 * d * E := by apply mul_le_mul_of_nonneg_left hEE; positivity
  have e3 : (8 / Γ + 6 * E) * d = 4 * (2 * d / Γ + d * E) + 2 * d * E := by field_simp; ring
  rw [e3]
  linarith

end GlobalTheory.Core.Rk
