import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

set_option autoImplicit false

namespace ReciprocityTheory.ChartRestriction.G.DVR.TWM

open ReciprocityTheory.ChartRestriction.G.Out

/- English proof (translation)
Introduce `_ _ _ _ _ hϖ _ _ hQ _ _ _ _ hv _ hk p m hm α G₀ hG₀ t ht` and use `v_ratio_gt hϖ hv hQ hk p m hm α G₀ hG₀ t ht`.
-/
theorem vRatioGt : VRatioGtStatement :=
  fun _ _ _ _ _ hϖ _ _ hQ _ _ _ _ hv _ hk p m hm α G₀ hG₀ t ht => v_ratio_gt hϖ hv hQ hk p m hm α G₀ hG₀ t ht

/- English proof (translation)
The claim follows from `tw_of hL.globalFns (twistBCSpan_of hT) vRatioGt`.
-/
theorem tw_of_laws (hL : Laws) (hT : TwistBaseChangeStatement) : TWStatement :=
  tw_of hL.globalFns (twistBCSpan_of hT) vRatioGt

end ReciprocityTheory.ChartRestriction.G.DVR.TWM
