import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.IntegralityGoodReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AltSmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ApplySmooth

noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

/- English proof (translation)
Introduce `V F _ _ _ _ _ _ Y hY hC l hl q w hw`. Take `⟨hlsm, hlpos, _⟩` from `hl`. Establish `hφY : ∀ p ∈ Y, l p • p ∈ Y` using `fun p hp => hC _ (hlpos p hp) p hp`. Establish `hφ : ∀ p ∈ Y, ContDiffAt ℝ ∞ (fun x => l x • x) p` using `fun p hp => (hlsm.contDiffAt (hY.mem_nhds hp)).smul contDiffAt_id`. Establish `hwat : ∀ p ∈ Y, ContDiffAt ℝ ∞ w (l p • p)` using `fun p hp => hw.contDiffAt (hY.mem_nhds (hφY p hp))`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `p hp`. Apply `ContDiffAt.contDiffWithinAt` to reduce the goal to its premises. Apply `altSmooth V V F q (pull l w) p` to reduce the goal to its premises. Introduce `v`.

Establish `hcomp : ContDiffAt ℝ ∞ (fun y => w (l y • y)) p` using `ContDiffAt.comp (g := w) (f := fun x => l x • x) p (hwat p hp) (hφ p hp)`. Establish `h` using `applySmooth V V F q (fun y => w (l y • y)) (fun i y => fderiv ℝ (fun x => l x • x) y (v i)) p hcomp (fun i => ((hφ p hp).fderiv_right (by simp)).clm_apply contDiffAt_const)`. Conclude with `h`. Introduce `p hp`. Conclude with `extDeriv_pullback ((hwat p hp).differentiableAt (by simp)) (hφ p hp) (by simpa using (WithTop.coe_le_coe.mpr le_top : (2 : WithTop ℕ∞) ≤ ∞))`.
-/
theorem pullB : PullB := by
  intro V F _ _ _ _ _ _ Y hY hC l hl q w hw
  obtain ⟨hlsm, hlpos, _⟩ := hl
  have hφY : ∀ p ∈ Y, l p • p ∈ Y := fun p hp => hC _ (hlpos p hp) p hp
  have hφ : ∀ p ∈ Y, ContDiffAt ℝ ∞ (fun x => l x • x) p := fun p hp =>
    (hlsm.contDiffAt (hY.mem_nhds hp)).smul contDiffAt_id
  have hwat : ∀ p ∈ Y, ContDiffAt ℝ ∞ w (l p • p) := fun p hp =>
    hw.contDiffAt (hY.mem_nhds (hφY p hp))
  refine ⟨?_, ?_⟩
  · intro p hp
    apply ContDiffAt.contDiffWithinAt
    apply altSmooth V V F q (pull l w) p
    intro v
    have hcomp : ContDiffAt ℝ ∞ (fun y => w (l y • y)) p :=
      ContDiffAt.comp (g := w) (f := fun x => l x • x) p (hwat p hp) (hφ p hp)
    have h := applySmooth V V F q (fun y => w (l y • y))
      (fun i y => fderiv ℝ (fun x => l x • x) y (v i)) p hcomp
      (fun i => ((hφ p hp).fderiv_right (by simp)).clm_apply contDiffAt_const)
    exact h
  · intro p hp
    exact extDeriv_pullback ((hwat p hp).differentiableAt (by simp)) (hφ p hp)
      (by simpa using (WithTop.coe_le_coe.mpr le_top : (2 : WithTop ℕ∞) ≤ ∞))

end UpperTheory.V.Lit.Dr
