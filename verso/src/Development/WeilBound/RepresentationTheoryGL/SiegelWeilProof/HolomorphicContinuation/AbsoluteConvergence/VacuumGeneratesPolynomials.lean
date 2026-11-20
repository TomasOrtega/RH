import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GenCoreTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TwoSided
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.NullIff
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.PolynomialDerivatives.LcOf

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw

/- English proof (translation)
The claim follows from `absThm_of lv (cyc_of fft) (lc_of fft) nullIff`.
-/
theorem absThm : AbsThm := absThm_of lv (cyc_of fft) (lc_of fft) nullIff

/- English proof (translation)
The claim follows from `genCore_top (cyc_of fft) (lc_of fft) nullIff`.
-/
theorem vacuum_generates_polynomials : GenCore := genCore_top (cyc_of fft) (lc_of fft) nullIff

end PositivityTheory.Rg.Sw.AbsSt
