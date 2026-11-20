import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

open MeasureTheory Matrix

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Introduce `n h y hy`. Use `set y' : Fin n → ℂ := fun i => y i with hy'def`. Establish `hy' : y' ≠ 0`. Introduce `hz`. Apply `hy` to reduce the goal to its premises.

Use extensionality with `i`. Conclude with `congrFun hz i`. Use `set φ : (Fin n → ℂ) → ℝ := fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y' with hφ`. Establish `hrw : (fun v => fsLog h (nrmv h v) (h.pointOf y)) = fun v => φ (h.mat *ᵥ v)`. Use function extensionality and compare the values at `v`.

Conclude with `h2 n h v y`. Take `⟨hint, hle, hmean⟩` from `h3 n y' hy'`. Establish `habs : (fun w => |φ w|) = fun w => -φ w`. Use function extensionality and compare the values at `w`. Conclude with `abs_of_nonpos (hle w)`.

Establish `hmeanAbs : ⨍ v in ballH h, |φ (h.mat *ᵥ v)| = (harmonic (n - 1) : ℝ) / 2`. Rewrite using `[(h1 n h (fun w => |φ w|)).2, habs, average_neg, hmean]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨_, hfin⟩` from `h4 n h`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hrw]`. Conclude with `(h1 n h φ).1.mpr hint`. Simplify using `only [show ∀ v, fsLog h (nrmv h v) (h.pointOf y) = φ (h.mat *ᵥ v) from fun v => h2 n h v y]`. Rewrite using `[← measure_smul_setAverage _ hfin.ne, hmeanAbs, smul_eq_mul, measureReal_def]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hrw, (h1 n h φ).2]`. Conclude with `hmean`.
-/
theorem FsLogAverage.proof (h1 : BallAverageLinear.Statement) (h2 : FsLogPointOf.Statement)
    (h3 : SphereMeanLinearBall.Statement) (h4 : BallVolume.Statement) : FsLogAverage.Statement := by
  intro n h y hy
  set y' : Fin n → ℂ := fun i => y i with hy'def
  have hy' : y' ≠ 0 := by
    intro hz
    apply hy
    ext i
    exact congrFun hz i
  set φ : (Fin n → ℂ) → ℝ := fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y' with hφ
  have hrw : (fun v => fsLog h (nrmv h v) (h.pointOf y)) = fun v => φ (h.mat *ᵥ v) := by
    funext v
    exact h2 n h v y
  obtain ⟨hint, hle, hmean⟩ := h3 n y' hy'
  have habs : (fun w => |φ w|) = fun w => -φ w := by
    funext w
    exact abs_of_nonpos (hle w)
  have hmeanAbs : ⨍ v in ballH h, |φ (h.mat *ᵥ v)| = (harmonic (n - 1) : ℝ) / 2 := by
    rw [(h1 n h (fun w => |φ w|)).2, habs, average_neg, hmean]
    ring
  obtain ⟨_, hfin⟩ := h4 n h
  refine ⟨?_, ?_, ?_⟩
  · rw [hrw]
    exact (h1 n h φ).1.mpr hint
  · simp only [show ∀ v, fsLog h (nrmv h v) (h.pointOf y) = φ (h.mat *ᵥ v) from fun v => h2 n h v y]
    rw [← measure_smul_setAverage _ hfin.ne, hmeanAbs, smul_eq_mul, measureReal_def]
    ring
  · rw [hrw, (h1 n h φ).2]
    exact hmean

end GroundTheory.Heights₂.Heights
