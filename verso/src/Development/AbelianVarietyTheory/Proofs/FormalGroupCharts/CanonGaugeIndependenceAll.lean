import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.G2Assumption
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.TruncatedExpSecondEqFull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermExpAddAndEvConst
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonGaugeSubIsBiadd
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalSecondPointDerivativeSecondCoordinate
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SecondOrderMonomial
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.WickVanishOfHalf

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gaugeExp_holds : GaugeExpSt :=
  GE.gauge_exp_identity germ_expAdd_and_evConst.1 germ_expAdd_and_evConst.2 canonGauge_sub_isBiadd
    quadDeriv_of_biadditive HalfIdentity.halfSt

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem canonGauge_independence_all : AdmissibilitySecond ∧ GaugeExpSt ∧ GaugeIndependenceColumns ∧ NabTransSt :=
  ⟨G2.galois_twist_preserves_siegel_bound germ_expAdd_and_evConst.1 germ_expAdd_and_evConst.2 canonGauge_sub_isBiadd
      quadDeriv_of_biadditive (wickVanish_of_half HalfIdentity.halfSt),
    gaugeExp_holds, WickVanishing.gauge_second_columns_of_exp gaugeExp_holds, WickVanishing.connection_translation_of_poly ChartTrans.transPolySt⟩

end GlobalTheory
