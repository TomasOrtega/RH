import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
open Formalism.BasicNotions Formalism.MainNotions.S GlobalTheory.Core.Rk
open scoped InnerProductSpace

namespace GlobalTheory.Core.Rk

/- English proof (translation)
Introduce `D u hS hd hT`. Establish `hT' : (2 : ℝ) < ((D.mem u).A.T : ℝ)` using `by exact_mod_cast hT`. Establish `hpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) - 1` using `by linarith`. Use `set a : ℝ := -(1 / (((D.mem u).A.T : ℝ) - 1)) with ha`. Establish `ha1 : 1 / (((D.mem u).A.T : ℝ) - 1) < 1`.

Rewrite using `[div_lt_one hpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `ha0 : 0 < 1 / (((D.mem u).A.T : ℝ) - 1)` using `by positivity`. Establish `hb : -2 ≤ a` using `by rw [ha]; linarith`. Establish `hB` using `one_add_mul_le_pow hb D.R.f`.

Establish `hd' : (0 : ℝ) < (d0 D u : ℝ)` using `by exact_mod_cast hd`. Unfold `RamShare at hS`. Unfold `RamBig`. Establish `hbase : 0 < 1 - 1 / (((D.mem u).A.T : ℝ) - 1)` using `by linarith`. Establish `hp : 0 < (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f` using `pow_pos hbase _`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `: (0 : ℝ) < (dU D u : ℝ)` using `by rw [hS]; exact mul_pos hd' hp`. Conclude with `this` after adjusting the coercions. Rewrite using `[hS]`. Establish `e1 : 1 + a = 1 - 1 / (((D.mem u).A.T : ℝ) - 1)` using `by rw [ha]; ring`.

Rewrite `hB` using `[e1]`. Establish `e2 : 1 + (D.R.f : ℝ) * a = 1 - (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1)` using `by rw [ha]; ring`. Rewrite `hB` using `[e2]`. Rewrite using `[mul_comm ((d0 D u : ℝ))]`. Conclude with `mul_le_mul_of_nonneg_right hB hd'.le`.
-/
theorem ramBig_of_ramShare : ∀ (D : D7) (u : D.what₂.Word), RamShare D u → 0 < d0 D u → 2 < (D.mem u).A.T →
    RamBig D u ((D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1)) := by
  intro D u hS hd hT
  have hT' : (2 : ℝ) < ((D.mem u).A.T : ℝ) := by exact_mod_cast hT
  have hpos : (0 : ℝ) < ((D.mem u).A.T : ℝ) - 1 := by linarith
  set a : ℝ := -(1 / (((D.mem u).A.T : ℝ) - 1)) with ha
  have ha1 : 1 / (((D.mem u).A.T : ℝ) - 1) < 1 := by
    rw [div_lt_one hpos]; linarith
  have ha0 : 0 < 1 / (((D.mem u).A.T : ℝ) - 1) := by positivity
  have hb : -2 ≤ a := by rw [ha]; linarith
  have hB := one_add_mul_le_pow hb D.R.f
  have hd' : (0 : ℝ) < (d0 D u : ℝ) := by exact_mod_cast hd
  unfold RamShare at hS
  unfold RamBig
  have hbase : 0 < 1 - 1 / (((D.mem u).A.T : ℝ) - 1) := by linarith
  have hp : 0 < (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f := pow_pos hbase _
  refine ⟨?_, ?_⟩
  · have : (0 : ℝ) < (dU D u : ℝ) := by rw [hS]; exact mul_pos hd' hp
    exact_mod_cast this
  · rw [hS]
    have e1 : 1 + a = 1 - 1 / (((D.mem u).A.T : ℝ) - 1) := by rw [ha]; ring
    rw [e1] at hB
    have e2 : 1 + (D.R.f : ℝ) * a = 1 - (D.R.f : ℝ) / (((D.mem u).A.T : ℝ) - 1) := by rw [ha]; ring
    rw [e2] at hB
    rw [mul_comm ((d0 D u : ℝ))]
    exact mul_le_mul_of_nonneg_right hB hd'.le

end GlobalTheory.Core.Rk
