import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedKleimanTop
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsScaledFSHProps
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsZCombExpand
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedSectionStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsMixedTopAlgebra
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem MixedKleimanTop.proof (hFS : ScaledFSHProps.Statement) (hE : ZCombExpand.Statement)
    (hSec : MixedSectionStep.Statement) (hH : ScaledFSTopPos.Statement) (hA : MixedTopAlgebra.Statement) :
    MixedKleimanTop.Statement := by
  intro d hd hAt hLow K _ ι _ P P0 M II hII h1 hP h0 hsM hnM hcM hhM
  obtain ⟨hsH, hcH, hmH⟩ := hFS K ι P P0
  have haH : (scaledFSH ι).a = fun k => (((fun _ => 1 : K → ℕ) k : ℕ) : ℤ) := by
    rw [scaledFSH_a]; rfl
  have e0 : II K ι P d (fun _ => M) =
      (fun i : ℕ => II K ι P d (fun j : Fin d => if (j : ℕ) < d - i then M else scaledFSH ι)) 0 := by
    simp
  rw [e0]
  refine hA d (fun i : ℕ => II K ι P d (fun j : Fin d => if (j : ℕ) < d - i then M else scaledFSH ι)) hd
    (fun i hi1 hid => hLow K ι P P0 M (scaledFSH ι) (fun _ => 1) II hII h1 hP h0 hsM hnM hcM hhM haH hsH hmH hcH
      (d - i) (by omega)) ?_ ?_
  · simpa using hH K ι P d II hII h1 hP
  · intro q p _ hp hpos
    obtain ⟨e1, e2⟩ := hE K ι (II K ι) (hII K ι) P d M (scaledFSH ι) q p hP hsM.1 hsH.1
    rw [← e2 h1]
    exact hSec K ι P P0 d M (scaledFSH ι) II hII hd hP h0 hsM hnM hcM hhM (scaledFSH_a ι) hsH hmH hcH hAt q p hp
      (by rw [e1]; exact hpos)

end GroundTheory.Heights₂.Heights.HilbertSamuel
