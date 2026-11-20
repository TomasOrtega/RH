import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMixedBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionInterpIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

namespace BlockResolutionMixedIntegral

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Apply function extensionality and compare values at an arbitrary argument. Replace the relevant objects with their definitions. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem proof (hB : BlockResolutionMixedBridge.Statement) (hI : BlockResolutionInterpIntegral.Statement) :
    BlockResolutionMixedIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A' hdeg hA'
  rw [hI D K ι Ω d A' hdeg hA']
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL : ∀ j : Fin D, IsSmoothHerm (if j.val < i then A' else d.A) := fun j => by
    split_ifs
    · exact hA'
    · exact d.semipos.1
  have hpot : blockMixPot d.A A' D i = fun j z => Real.log ((if j.val < i then A' else d.A).h z) := by
    funext j z
    unfold blockMixPot
    split_ifs <;> rfl
  have hres : (fun j : Fin D => AnResBridge.potOf d.R (if j.val < i then A' else d.A)) =
      fun j : Fin D => if j.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A := by
    funext j
    split_ifs <;> rfl
  rw [hpot, hB D K ι Ω d (fun j => if j.val < i then A' else d.A) A' hL hdeg hA', hres]

end BlockResolutionMixedIntegral

end GroundTheory.Heights₂.Heights.HilbertSamuel
