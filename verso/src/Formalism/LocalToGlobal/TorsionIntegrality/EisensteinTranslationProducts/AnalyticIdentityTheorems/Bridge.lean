import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinS2LimitFormula
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorWp
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.TwoTorsionU

namespace Formalism.L2.Th1.F

/- English proof (translation)
Introduce `W L h2 h3`. Establish `h` using `hw ℂ W`. Rewrite `h` using `[h2, h3]`. Conclude with `hu ℂ L.g₂ L.g₃ _ _ h (ht L)`.
-/
theorem curveBridge_of (hw : Formalism.L2.Th1.A.BridgeWp) (hu : IsWpUnique) (ht : TaylorIsWp) : CurveBridge := by
  intro W L h2 h3
  have h := hw ℂ W
  rw [h2, h3] at h
  exact hu ℂ L.g₂ L.g₃ _ _ h (ht L)

/- English proof (translation)
The claim follows from `curveBridge_of Formalism.L2.Th1.A.bridgeWp weierstrass_series_unique (taylorIsWp_of taylor_ring taylor_deriv)`.
-/
theorem curve_weierstrass_series_eq : CurveBridge :=
  curveBridge_of Formalism.L2.Th1.A.bridgeWp weierstrass_series_unique (taylorIsWp_of taylor_ring taylor_deriv)

end Formalism.L2.Th1.F
