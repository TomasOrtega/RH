import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo

namespace FubiniStudySmooth

/- English proof (translation)
Establish `hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : (Σ k, ι k) → ℂ => WithLp.toLp 2 (fun i => w ⟨k, i⟩))` using `PiLp.contDiff_toLp.comp (contDiff_pi.2 fun i => contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))`. Establish `hne : WithLp.toLp 2 (fun i => z ⟨k, i⟩) ≠ 0`. Take `⟨i, hi⟩` from `hz`. Introduce `h0`. Conclude with `hi (by simpa using congrArg (fun v : WithLp 2 (ι k → ℂ) => v.ofLp i) h0)`.

Conclude with `(contDiffAt_norm ℂ hne).comp z hL.contDiffAt`.
-/
theorem contDiffAt_blockNorm {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (k : K)
    (z : (Σ k, ι k) → ℂ) (hz : ∃ i, z ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => ‖WithLp.toLp 2 (fun i => w ⟨k, i⟩)‖) z := by
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w : (Σ k, ι k) → ℂ => WithLp.toLp 2 (fun i => w ⟨k, i⟩)) :=
    PiLp.contDiff_toLp.comp (contDiff_pi.2 fun i => contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))
  have hne : WithLp.toLp 2 (fun i => z ⟨k, i⟩) ≠ 0 := by
    obtain ⟨i, hi⟩ := hz
    intro h0
    exact hi (by simpa using congrArg (fun v : WithLp 2 (ι k → ℂ) => v.ofLp i) h0)
  exact (contDiffAt_norm ℂ hne).comp z hL.contDiffAt

end FubiniStudySmooth

/- English proof (translation)
Introduce `K _ ι _`. Use `show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ ^ ((1 : K → ℤ) k)) _`. Use `contDiffOn_prod fun k _ => ?_` and prove the remaining obligations. Introduce `z hz`. Simplify using `only [Pi.one_apply, zpow_one]`.

Conclude with `(FubiniStudySmooth.contDiffAt_blockNorm ι k z (hz k)).contDiffWithinAt`.
-/
theorem FsLineSmooth.proof : FsLineSmooth.Statement := by
  intro K _ ι _
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : (Σ k, ι k) → ℂ => ∏ k, ‖WithLp.toLp 2 (fun i => z ⟨k, i⟩)‖ ^ ((1 : K → ℤ) k)) _
  refine contDiffOn_prod fun k _ => ?_
  intro z hz
  simp only [Pi.one_apply, zpow_one]
  exact (FubiniStudySmooth.contDiffAt_blockNorm ι k z (hz k)).contDiffWithinAt

end GroundTheory.Heights₂.Heights
