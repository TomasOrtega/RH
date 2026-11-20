import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated

open MeasureTheory Filter Topology
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.RgAds

/- English proof (translation)
Introduce `X _ m U F hU hmeas hdiff hdom`. Use `(GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := m) (F := fun x s => F s x) hU hmeas (Eventually.of_forall hdiff) ?_).1` and prove the remaining obligations. Introduce `s₀ hs₀`. Take `⟨g, hg, hev⟩` from `hdom s₀ hs₀`. Conclude with `⟨{s | ∀ x, ‖F s x‖ ≤ g x}, hev, g, hg, ae_of_all _ fun x s hs => hs x⟩`.
-/
theorem holomorphy_integral_param : HI := by
  intro X _ m U F hU hmeas hdiff hdom
  refine (GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated (μ := m)
    (F := fun x s => F s x) hU hmeas (Eventually.of_forall hdiff) ?_).1
  intro s₀ hs₀
  obtain ⟨g, hg, hev⟩ := hdom s₀ hs₀
  exact ⟨{s | ∀ x, ‖F s x‖ ≤ g x}, hev, g, hg, ae_of_all _ fun x s hs => hs x⟩

end GlobalTheory.CompanionTheory.RgAds
