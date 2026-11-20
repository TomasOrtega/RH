import Formalism.TruncatedSeriesCounting.LemmaDetPoly

open Formalism.NG

universe u v w

namespace Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

/- English proof (authored)
Apply the determinant comparison input with the supplied ring action and element Θ. Its remaining premise is the product congruence for an arbitrary tuple of elements of R′ and a test point. View each tuple entry as a matrix-valued function over the fraction field. The hypothesis on R′ gives the action compatibility for each of these functions, so the product congruence input applies and supplies the premise.
-/
theorem eta_determinant_comparison : BridgeDet.{u, v, w} := by
  intro hP hB O _ _ X' G _ T' d _ _ R' ρ hρ hR g _ _ Θ
  refine hB O X' T' d R' ?_ g Θ
  intro m a s
  exact hP O (FractionRing O) X' G d T' ρ hρ m (fun i => (a i : X' → Matrix d d (FractionRing O)))
    (fun i => hR _ (a i).2) s

end Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities
