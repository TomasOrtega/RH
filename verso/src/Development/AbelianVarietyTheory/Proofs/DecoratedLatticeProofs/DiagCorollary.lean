import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

/- English proof (translation)
Rewrite using `[← D.Dstar_eq u]`. Conclude with `(D.mem u).A.Dstar_pos`.
-/
theorem dstar_pos_of (D : D7) (u : D.what₂.Word) : 0 < D.what₂.Dstar := by
  rw [← D.Dstar_eq u]; exact (D.mem u).A.Dstar_pos

/- English proof (translation)
Unfold `DiagS at *`. Conclude with `h.trans (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))`.
-/
theorem diagS_mono {D : D7} {u : D.what₂.Word} {e e' : ℝ} (h : DiagS D u e) (he : e ≤ e') : DiagS D u e' := by
  unfold DiagS at *
  exact h.trans (mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _))

/- English proof (translation)
Unfold `kfk`. Conclude with `mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.log_natCast_nonneg _)`.
-/
theorem kfk_nonneg (D : D7) : 0 ≤ kfk D := by
  unfold kfk
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.log_natCast_nonneg _)

/- English proof (translation)
Establish `first : ∀ (D : D7) (u : D.what₂.Word) (A x κ : ℝ), 0 ≤ A → TwoTerm D u A x → (d0 D u : ℝ) ≤ κ * D.what₂.Dstar → DiagS D u (A * κ + x)`. Introduce `D u A x κ hA h hd`. Establish `hD` using `dstar_pos_of D u`. Establish `hd0 : (0 : ℝ) ≤ (d0 D u : ℝ)` using `Nat.cast_nonneg _`. Establish `hq : (d0 D u : ℝ) ^ 2 / D.what₂.Dstar ≤ κ * (d0 D u : ℝ)`.

Rewrite using `[div_le_iff₀ hD]`. Use `mul_le_mul_of_nonneg_left hd hd0` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Unfold `DiagS`. Unfold `TwoTerm at h`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨first, ?_, ?_⟩` and prove the remaining obligations. Introduce `D u L C hc hS hSm set c := C * mfL D L with hcdef`. Establish `h2 : Real.exp (-(2 * C * mfL D L)) = Real.exp (-c) * Real.exp (-c)`. Rewrite using `[← Real.exp_add]`.

Use `congr 1`. Rewrite using `[hcdef]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1 : Real.exp c * Real.exp (-c) = 1` using `by rw [← Real.exp_add]; simp`. Establish `hle : Real.exp (-c) ≤ 1` using `Real.exp_le_one_iff.2 (by linarith)`.

Establish `hpos : 0 < Real.exp (-c)` using `Real.exp_pos _`. Establish `hk` using `kfk_nonneg D`. Establish `hkk : Real.exp (-kfk D) ≤ Real.exp (-(kfk D / 2))` using `Real.exp_le_exp.2 (by linarith)`. Establish `hd` using `first D u (4 * (Real.exp c + 1)) (4 * Real.exp (-(kfk D / 2)) + 2 * Real.exp (-kfk D)) (Real.exp (-(2 * C * mfL D L))) (by positivity) hS (by unfold Small at hSm; linarith [hSm])`. Use `diagS_mono hd ?_` and prove the remaining obligations.

Unfold `eDiag`. Rewrite using `[h2, ← hcdef]`. Establish `: 4 * (Real.exp c + 1) * (Real.exp (-c) * Real.exp (-c)) = 4 * Real.exp (-c) + 4 * (Real.exp (-c) * Real.exp (-c))`. Establish `e : 4 * (Real.exp c + 1) * (Real.exp (-c) * Real.exp (-c)) = 4 * (Real.exp c * Real.exp (-c)) * Real.exp (-c) + 4 * (Real.exp (-c) * Real.exp (-c))` using `by ring`. Rewrite using `[e, h1]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Use the polynomial consequences of the given equalities and inequalities. Introduce `D u Γ₀`. Unfold `SAbs TwoTerm`.

Rewrite using `[show (1 / 4 : ℝ) * (d0 D u : ℝ) = (d0 D u : ℝ) / 4 by ring]`.
-/
theorem diag_corollary :
    (∀ (D : D7) (u : D.what₂.Word) (A x κ : ℝ), 0 ≤ A → TwoTerm D u A x → (d0 D u : ℝ) ≤ κ * D.what₂.Dstar →
      DiagS D u (A * κ + x)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (L C : ℝ), 0 ≤ C * mfL D L → SDiag D u L C → Small D u L C →
      DiagS D u (eDiag D L C)) ∧
    (∀ (D : D7) (u : D.what₂.Word) (Γ₀ : ℝ), SAbs D u Γ₀ ↔ TwoTerm D u Γ₀ (1 / 4)) := by
  have first : ∀ (D : D7) (u : D.what₂.Word) (A x κ : ℝ), 0 ≤ A → TwoTerm D u A x → (d0 D u : ℝ) ≤ κ * D.what₂.Dstar →
      DiagS D u (A * κ + x) := by
    intro D u A x κ hA h hd
    have hD := dstar_pos_of D u
    have hd0 : (0 : ℝ) ≤ (d0 D u : ℝ) := Nat.cast_nonneg _
    have hq : (d0 D u : ℝ) ^ 2 / D.what₂.Dstar ≤ κ * (d0 D u : ℝ) := by
      rw [div_le_iff₀ hD]
      have := mul_le_mul_of_nonneg_left hd hd0
      nlinarith
    unfold DiagS
    unfold TwoTerm at h
    calc hsDev D u ≤ A * (d0 D u : ℝ) ^ 2 / D.what₂.Dstar + x * (d0 D u : ℝ) := h
      _ = A * ((d0 D u : ℝ) ^ 2 / D.what₂.Dstar) + x * (d0 D u : ℝ) := by rw [mul_div_assoc]
      _ ≤ A * (κ * (d0 D u : ℝ)) + x * (d0 D u : ℝ) := by gcongr
      _ = (A * κ + x) * (d0 D u : ℝ) := by ring
  refine ⟨first, ?_, ?_⟩
  · intro D u L C hc hS hSm
    set c := C * mfL D L with hcdef
    have h2 : Real.exp (-(2 * C * mfL D L)) = Real.exp (-c) * Real.exp (-c) := by
      rw [← Real.exp_add]; congr 1; rw [hcdef]; ring
    have h1 : Real.exp c * Real.exp (-c) = 1 := by rw [← Real.exp_add]; simp
    have hle : Real.exp (-c) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hpos : 0 < Real.exp (-c) := Real.exp_pos _
    have hk := kfk_nonneg D
    have hkk : Real.exp (-kfk D) ≤ Real.exp (-(kfk D / 2)) := Real.exp_le_exp.2 (by linarith)
    have hd := first D u (4 * (Real.exp c + 1)) (4 * Real.exp (-(kfk D / 2)) + 2 * Real.exp (-kfk D))
      (Real.exp (-(2 * C * mfL D L))) (by positivity) hS (by unfold Small at hSm; linarith [hSm])
    refine diagS_mono hd ?_
    unfold eDiag
    rw [h2, ← hcdef]
    have : 4 * (Real.exp c + 1) * (Real.exp (-c) * Real.exp (-c)) = 4 * Real.exp (-c) + 4 * (Real.exp (-c) * Real.exp (-c)) := by
      have e : 4 * (Real.exp c + 1) * (Real.exp (-c) * Real.exp (-c))
          = 4 * (Real.exp c * Real.exp (-c)) * Real.exp (-c) + 4 * (Real.exp (-c) * Real.exp (-c)) := by ring
      rw [e, h1]; ring
    rw [this]
    nlinarith
  · intro D u Γ₀
    unfold SAbs TwoTerm
    rw [show (1 / 4 : ℝ) * (d0 D u : ℝ) = (d0 D u : ℝ) / 4 by ring]

end GlobalTheory.Core.Rk
