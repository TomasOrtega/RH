import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarSlabMeasure
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietySlabMeasure
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

/- English proof (translation)
Introduce `n d J u R hJ hd hu`. Take `⟨C, α, -, hα, hb⟩` from `hV n d J u hJ hd.le hu R`. Use `⟨C, α, hα, fun ε hε hε1 => ?_⟩` and prove the remaining obligations. Establish `hset : zeroSetEuc J ∩ {z | ‖z‖ ≤ R} ∩ {z | ‖∑ j, u j * z j‖ ≤ ε} = {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε}`. Use extensionality with `z`.

Simplify using `only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]`. Rewrite using `[hset]`. Conclude with `hb ε hε hε1`.
-/
theorem VarSlabMeasure.proof (hV : VarietySlabMeasure.Statement) : VarSlabMeasure.Statement := by
  intro n d J u R hJ hd hu
  obtain ⟨C, α, -, hα, hb⟩ := hV n d J u hJ hd.le hu R
  refine ⟨C, α, hα, fun ε hε hε1 => ?_⟩
  have hset : zeroSetEuc J ∩ {z | ‖z‖ ≤ R} ∩ {z | ‖∑ j, u j * z j‖ ≤ ε} =
      {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  rw [hset]
  exact hb ε hε hε1

end

end GroundTheory.Heights₂.Heights
