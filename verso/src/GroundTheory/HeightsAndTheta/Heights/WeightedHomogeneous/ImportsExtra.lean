import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AddBlockEquivSymmChartRingMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hA ι _ _ n P D G`. Take `⟨h1, h2⟩` from `hA ι n P (AddBlockData.toObjects D) G.d G.g G.isFormSystem`. Use `⟨fun c i j ↦ ?_, fun w hw ↦ ?_⟩` and prove the remaining obligations. Establish `e : (AddBlockData.toObjects D).extIdeal = D.ext` using `AddBlockEq.addBlockEquiv_symm_extIdeal D`.

Use `h1 c i j` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this`. Establish `e : (AddBlockData.toObjects D).extPoints = conePoints D.ext ℂ` using `AddBlockEq.addBlockEquiv_symm_conePoints D`. Rewrite `hw` using `[← e]`.

Conclude with `h2 w hw`. Introduce `hB ι _ _ n P D d g hg`. Take `⟨h1, h2⟩` from `hB ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem hg)`. Establish `e : (AddBlockData.ofObjects D).ext = D.extIdeal` using `AddBlockEq.addBlockEquiv_extIdeal D`. Use `⟨fun c i j ↦ ?_, fun w hw ↦ ?_⟩` and prove the remaining obligations.

Use `h1 c i j` as an intermediate fact. Rewrite `this` using `[e]`. Conclude with `this`. Establish `e' : D.extPoints = conePoints (AddBlockData.ofObjects D).ext ℂ` using `AddBlockEq.extPoints_eq D`. Rewrite `hw` using `[e']`.

Conclude with `h2 w hw`.
-/
theorem ConePoints.equiv :
    GroundTheory.Heights₂.Heights.ConePoints.Statement ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.ConePoints.Statement := by
  constructor
  · intro hA ι _ _ n P D G
    obtain ⟨h1, h2⟩ := hA ι n P (AddBlockData.toObjects D) G.d G.g G.isFormSystem
    refine ⟨fun c i j ↦ ?_, fun w hw ↦ ?_⟩
    · have e : (AddBlockData.toObjects D).extIdeal = D.ext := AddBlockEq.addBlockEquiv_symm_extIdeal D
      have := h1 c i j
      rw [e] at this
      exact this
    · have e : (AddBlockData.toObjects D).extPoints = conePoints D.ext ℂ :=
        AddBlockEq.addBlockEquiv_symm_conePoints D
      rw [← e] at hw
      exact h2 w hw
  · intro hB ι _ _ n P D d g hg
    obtain ⟨h1, h2⟩ := hB ι n P (AddBlockData.ofObjects D) (ChartForms.ofFormSystem hg)
    have e : (AddBlockData.ofObjects D).ext = D.extIdeal := AddBlockEq.addBlockEquiv_extIdeal D
    refine ⟨fun c i j ↦ ?_, fun w hw ↦ ?_⟩
    · have := h1 c i j
      rw [e] at this
      exact this
    · have e' : D.extPoints = conePoints (AddBlockData.ofObjects D).ext ℂ := AddBlockEq.extPoints_eq D
      rw [e'] at hw
      exact h2 w hw

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
