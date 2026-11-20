import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceUnmixedGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMHeightOneGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimDomain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLocalDimGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceCMUnmixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

/- English proof (translation)
Introduce `n d J W u hJ hdim hu hW`. Take `⟨f, hfW, hf⟩` from `hA n J W (linForm u) hJ hu hW`. Use `⟨f, hfW, fun q hq hfq => ?_⟩` and prove the remaining obligations. Establish `hqJ : q ∈ zeroSet J` using `fun g hg => hq g (hW.1.2 (Ideal.mem_sup_left hg))`. Take `⟨O, hOo, hOd, hO⟩` from `hB n d J q hJ hdim hqJ`.

Conclude with `⟨O, hOo, hOd, fun L hL => hD n d J L q (hf q hq hfq) (hC n (d + 1) J hJ hdim q hqJ) (hO L hL)⟩`.
-/
theorem SliceUnmixedGeneral.proof (hA : CMHeightOneGeneral.Statement) (hC : LocalDimDomain.Statement)
    (hB : SliceLocalDimGeneral.Statement) (hD : SliceCMUnmixed.Statement) :
    SliceUnmixedGeneral.Statement := by
  intro n d J W u hJ hdim hu hW
  obtain ⟨f, hfW, hf⟩ := hA n J W (linForm u) hJ hu hW
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  have hqJ : q ∈ zeroSet J := fun g hg => hq g (hW.1.2 (Ideal.mem_sup_left hg))
  obtain ⟨O, hOo, hOd, hO⟩ := hB n d J q hJ hdim hqJ
  exact ⟨O, hOo, hOd, fun L hL =>
    hD n d J L q (hf q hq hfq) (hC n (d + 1) J hJ hdim q hqJ) (hO L hL)⟩

end GroundTheory.Heights₂.Heights
