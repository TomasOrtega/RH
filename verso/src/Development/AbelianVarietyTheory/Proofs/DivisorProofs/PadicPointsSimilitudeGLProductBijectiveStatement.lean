import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicPointsSimilitudeGLProductBijective
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
open GlobalTheory.LKTrip
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.padicPoints_similitude_GL_product_bijective : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), Function.Bijective G.localization₂ := by
  first | (exact @GlobalTheory.LKTrip.HTGroup.bijective_locP) | (exact GlobalTheory.LKTrip.HTGroup.bijective_locP) | (intros; apply GlobalTheory.LKTrip.HTGroup.bijective_locP  <;> assumption)
