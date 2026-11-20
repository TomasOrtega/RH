import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel

/- English proof (translation)
Introduce `H _ _ _ _ _ _ _ _ n ι hemb C hC`. Establish `hK : IsCompact (matCoord ι '' C)` using `hC.image hemb.continuous`. Take `⟨r, hr⟩` from `hK.isBounded.subset_closedBall 0`. Set `f : ContDiffBump (0 : Fin n → Fin n → ℂ)` to `⟨max r 1, max r 1 + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩`. Use `⟨fun g => ((f (matCoord ι g) : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Use `HasCompactSupport.intro (hemb.isCompact_preimage (isCompact_closedBall (0 : Fin n → Fin n → ℂ) (max r 1 + 1))) ?_` and prove the remaining obligations. Introduce `g hg`. Simplify using `only [Set.mem_preimage, Metric.mem_closedBall, not_le] at hg`. Establish `: f (matCoord ι g) = 0` using `f.zero_of_le_dist hg.le`. Simplify using `[this]`.

Use `⟨fun x => ((f x : ℝ) : ℂ), ?_, fun g => rfl⟩` and prove the remaining obligations. Conclude with `Complex.ofRealCLM.contDiff.comp f.contDiff`. Introduce `y hy`. Establish `hm : matCoord ι y ∈ Metric.closedBall (0 : Fin n → Fin n → ℂ) (max r 1)` using `Metric.closedBall_subset_closedBall (le_max_left _ _) (hr ⟨y, hy, rfl⟩)`. Establish `: f (matCoord ι y) = 1` using `f.one_of_mem_closedBall hm`.

Simplify using `[this]`.
-/
theorem bumpOn : BumpOn := by
  intro H _ _ _ _ _ _ _ _ n ι hemb C hC
  have hK : IsCompact (matCoord ι '' C) := hC.image hemb.continuous
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
  let f : ContDiffBump (0 : Fin n → Fin n → ℂ) :=
    ⟨max r 1, max r 1 + 1, lt_of_lt_of_le one_pos (le_max_right _ _), by linarith⟩
  refine ⟨fun g => ((f (matCoord ι g) : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · refine HasCompactSupport.intro (hemb.isCompact_preimage (isCompact_closedBall (0 : Fin n → Fin n → ℂ) (max r 1 + 1))) ?_
    intro g hg
    simp only [Set.mem_preimage, Metric.mem_closedBall, not_le] at hg
    have : f (matCoord ι g) = 0 := f.zero_of_le_dist hg.le
    simp [this]
  · refine ⟨fun x => ((f x : ℝ) : ℂ), ?_, fun g => rfl⟩
    exact Complex.ofRealCLM.contDiff.comp f.contDiff
  · intro y hy
    have hm : matCoord ι y ∈ Metric.closedBall (0 : Fin n → Fin n → ℂ) (max r 1) :=
      Metric.closedBall_subset_closedBall (le_max_left _ _) (hr ⟨y, hy, rfl⟩)
    have : f (matCoord ι y) = 1 := f.one_of_mem_closedBall hm
    simp [this]

end MainStatements.WeightKernel

end
