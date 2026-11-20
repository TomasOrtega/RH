import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSFG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsSmoothExt
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH.SFG

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `k r E _ _ F hF hc`. Use `haveI : ProperSpace (B.Mat k r) := FiniteDimensional.proper ℝ _`. Take `⟨R, hR⟩` from `hc.isCompact.isBounded.subset_ball (0 : B.Mat k r)`. Use `choose U f' hUo hmem hsm hag using hF`. Set `V : B.GV k r → Set (B.Mat k r)` to `fun i => U i.1 i.2 ∩ Metric.ball 0 R`.

Establish `hVo : ∀ i, IsOpen (V i)` using `fun i => (hUo i.1 i.2).inter Metric.isOpen_ball`. Establish `hs : IsClosed (tsupport F ∩ B.GV k r)` using `(isClosed_tsupport F).inter B5.GV_closed`. Establish `hcov : tsupport F ∩ B.GV k r ⊆ ⋃ i, V i`. Introduce `x hx`. Conclude with `Set.mem_iUnion.2 ⟨⟨x, hx.2⟩, hmem x hx.2, hR hx.1⟩`.

Take `⟨ρ, hρ⟩` from `@SmoothPartitionOfUnity.exists_isSubordinate _ (B.Mat k r) _ _ (B.Mat k r) _ (modelWithCornersSelf ℝ (B.Mat k r)) (B.Mat k r) _ (chartedSpaceSelf _) _ _ _ _ _ hs V hVo hcov`. Use `⟨fun x => ∑ᶠ i, ρ i x • f' i.1 i.2 x, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[contDiff_iff_contDiffAt]`. Introduce `x`. Use `ρ.contDiffAt_finsum fun i hi => ?_` and prove the remaining obligations.

Establish `hx : x ∈ U i.1 i.2` using `(hρ i hi).1`. Conclude with `(hsm i.1 i.2).contDiffAt ((hUo i.1 i.2).mem_nhds hx)`. Use `HasCompactSupport.intro (isCompact_closedBall (0 : B.Mat k r) R) fun x hx => ?_` and prove the remaining obligations. Establish `h0 : ∀ i, ρ i x = 0` using `fun i => by`. Assume the negation of the conclusion as `h`.

Conclude with `hx (Metric.ball_subset_closedBall (hρ i (subset_tsupport _ h)).2)`. Simplify using `[h0]`. Introduce `g hg`. Establish `key : ∀ i, ρ i g • f' i.1 i.2 g = ρ i g • F g` using `fun i => by`. Distinguish the cases in `h : ρ i g = 0`.

Simplify using `[h]`. Rewrite using `[← hag i.1 i.2 g (hρ i (subset_tsupport _ h)).1 hg]`. Simplify using `only [key]`. Rewrite using `[← finsum_smul]`. Distinguish the cases in `hF0 : g ∈ tsupport F`.

Rewrite using `[ρ.sum_eq_one ⟨hF0, hg⟩, one_smul]`. Rewrite using `[image_eq_zero_of_notMem_tsupport hF0, smul_zero]`.
-/
theorem ckExt_proof : CkExt := by
  intro k r E _ _ F hF hc
  haveI : ProperSpace (B.Mat k r) := FiniteDimensional.proper ℝ _
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_ball (0 : B.Mat k r)
  choose U f' hUo hmem hsm hag using hF
  let V : B.GV k r → Set (B.Mat k r) := fun i => U i.1 i.2 ∩ Metric.ball 0 R
  have hVo : ∀ i, IsOpen (V i) := fun i => (hUo i.1 i.2).inter Metric.isOpen_ball
  have hs : IsClosed (tsupport F ∩ B.GV k r) := (isClosed_tsupport F).inter B5.GV_closed
  have hcov : tsupport F ∩ B.GV k r ⊆ ⋃ i, V i := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx.2⟩, hmem x hx.2, hR hx.1⟩
  obtain ⟨ρ, hρ⟩ := @SmoothPartitionOfUnity.exists_isSubordinate _ (B.Mat k r) _ _ (B.Mat k r) _
    (modelWithCornersSelf ℝ (B.Mat k r)) (B.Mat k r) _ (chartedSpaceSelf _) _ _ _ _ _ hs V hVo hcov
  refine ⟨fun x => ∑ᶠ i, ρ i x • f' i.1 i.2 x, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    refine ρ.contDiffAt_finsum fun i hi => ?_
    have hx : x ∈ U i.1 i.2 := (hρ i hi).1
    exact (hsm i.1 i.2).contDiffAt ((hUo i.1 i.2).mem_nhds hx)
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : B.Mat k r) R) fun x hx => ?_
    have h0 : ∀ i, ρ i x = 0 := fun i => by
      by_contra h
      exact hx (Metric.ball_subset_closedBall (hρ i (subset_tsupport _ h)).2)
    simp [h0]
  · intro g hg
    have key : ∀ i, ρ i g • f' i.1 i.2 g = ρ i g • F g := fun i => by
      by_cases h : ρ i g = 0
      · simp [h]
      · rw [← hag i.1 i.2 g (hρ i (subset_tsupport _ h)).1 hg]
    simp only [key]
    rw [← finsum_smul]
    by_cases hF0 : g ∈ tsupport F
    · rw [ρ.sum_eq_one ⟨hF0, hg⟩, one_smul]
    · rw [image_eq_zero_of_notMem_tsupport hF0, smul_zero]

end Formalism.FourierDecayAlt.P.CutSH.SFG
