import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionMixedBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBlockResolutionInterpIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

namespace BlockResolutionMixedIntegral

/- English proof (translation)
Introduce `D K _ _ ι _ Ω _ _ d A' hdeg hA'`. Rewrite using `[hI D K ι Ω d A' hdeg hA']`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hL : ∀ j : Fin D, IsSmoothHerm (if j.val < i then A' else d.A)` using `fun j => by split_ifs`. Conclude with `hA'`.

Conclude with `d.semipos.1`. Establish `hpot : blockMixPot d.A A' D i = fun j z => Real.log ((if j.val < i then A' else d.A).h z)`. Use function extensionality and compare the values at `j z`. Unfold `blockMixPot`. Apply the tactic sequence `split_ifs <;> rfl`.

Establish `hres : (fun j : Fin D => AnResBridge.potOf d.R (if j.val < i then A' else d.A)) = fun j : Fin D => if j.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[hpot, hB D K ι Ω d (fun j => if j.val < i then A' else d.A) A' hL hdeg hA', hres]`.
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
