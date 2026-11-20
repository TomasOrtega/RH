import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedIntegral
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedBridge
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionInterpIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

namespace ResolutionMixedIntegral

/- English proof (translation)
Introduce `D Ω _ _ κ _ d m₁ hm₁`. Rewrite using `[hI D Ω κ d m₁ hm₁]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hM : ∀ j : Fin D, IsSmoothMetric (if j.val < i then m₁ else d.m)` using `fun j => by split_ifs`. Conclude with `hm₁`.

Conclude with `d.smooth`. Establish `hpot : mixPot d.m m₁ D i = fun j z => Real.log ((if j.val < i then m₁ else d.m).ρ z)`. Use function extensionality and compare the values at `j z`. Unfold `mixPot`. Apply the tactic sequence `split_ifs <;> rfl`.

Establish `hres : (fun j : Fin D => resPot d (if j.val < i then m₁ else d.m)) = fun j : Fin D => if j.val < i then resPot d m₁ else resPot d d.m`. Use function extensionality and compare the values at `j`. Apply the tactic sequence `split_ifs <;> rfl`. Rewrite using `[hpot, hB D Ω κ d (fun j => if j.val < i then m₁ else d.m) m₁ hM hm₁, hres]`.
-/
theorem proof (hB : ResolutionMixedBridge.Statement) (hI : ResolutionInterpIntegral.Statement) :
    ResolutionMixedIntegral.Statement := by
  intro D Ω _ _ κ _ d m₁ hm₁
  rw [hI D Ω κ d m₁ hm₁]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hM : ∀ j : Fin D, IsSmoothMetric (if j.val < i then m₁ else d.m) := fun j => by
    split_ifs
    · exact hm₁
    · exact d.smooth
  have hpot : mixPot d.m m₁ D i = fun j z => Real.log ((if j.val < i then m₁ else d.m).ρ z) := by
    funext j z
    unfold mixPot
    split_ifs <;> rfl
  have hres : (fun j : Fin D => resPot d (if j.val < i then m₁ else d.m)) =
      fun j : Fin D => if j.val < i then resPot d m₁ else resPot d d.m := by
    funext j
    split_ifs <;> rfl
  rw [hpot, hB D Ω κ d (fun j => if j.val < i then m₁ else d.m) m₁ hM hm₁, hres]

end ResolutionMixedIntegral

end GroundTheory.Heights₂.Heights.HilbertSamuel
