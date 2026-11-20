import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.AddBlockEquivSymmChartRingMap
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.ExistsChartFormsIffIsFormSystem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open MvPolynomial

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hA ι _ _ n P D G c j hg W`. Establish `e : (AddBlockEq.split_model_to_place_model D).extIdeal = D.ext` using `AddBlockEq.addBlockEquiv_symm_extIdeal D`. Establish `h` using `hA ι n P (AddBlockEq.split_model_to_place_model D) G.d G.g G.isFormSystem c j (by rw [e]; exact hg) W`. Rewrite `h` using `[e]`.

Conclude with `h`. Introduce `hB ι _ _ n P D d g hfs c j hg W`. Establish `e : (AddBlockEq.toIndefiniteRowSideFullHecke D).ext = D.extIdeal` using `AddBlockEq.addBlockEquiv_extIdeal D`. Establish `h` using `hB ι n P (AddBlockEq.toIndefiniteRowSideFullHecke D) (ChartForms.ofFormSystem hfs) c j (by rw [e]; exact hg) W`. Rewrite `h` using `[e]`.

Conclude with `h`.
-/
theorem SectionCycle.equiv :
    GroundTheory.Heights₂.Heights.SectionCycle.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.SectionCycle.Statement := by
  constructor
  · intro hA ι _ _ n P D G c j hg W
    have e : (AddBlockEq.split_model_to_place_model D).extIdeal = D.ext := AddBlockEq.addBlockEquiv_symm_extIdeal D
    have h := hA ι n P (AddBlockEq.split_model_to_place_model D) G.d G.g G.isFormSystem c j
      (by rw [e]; exact hg) W
    rw [e] at h
    exact h
  · intro hB ι _ _ n P D d g hfs c j hg W
    have e : (AddBlockEq.toIndefiniteRowSideFullHecke D).ext = D.extIdeal := AddBlockEq.addBlockEquiv_extIdeal D
    have h := hB ι n P (AddBlockEq.toIndefiniteRowSideFullHecke D) (ChartForms.ofFormSystem hfs) c j
      (by rw [e]; exact hg) W
    rw [e] at h
    exact h

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
