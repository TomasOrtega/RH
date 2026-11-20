import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.LanglandsDataDualGLOfCosocle
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.EssSquareIntegrableSegmentsHolds
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.ProvedMore
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesMore
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero

namespace UpperTheory.Zero.LLC.Pr

/- English proof (translation)
The claim follows from `PositivityTheory.Exh.langlandsExhaustionGL_holds`.
-/
theorem exh : GlobalTheory.Published.LanglandsExhaustionGL := PositivityTheory.Exh.langlandsExhaustionGL_holds
/- English proof (translation)
The claim follows from `PositivityTheory.Exh.langlandsMultisegments_holds`.
-/
theorem multi : GlobalTheory.Published.LanglandsMultisegments := PositivityTheory.Exh.langlandsMultisegments_holds
/- English proof (translation)
The claim follows from `PositivityTheory.Exh.standardCosocleGL_holds`.
-/
theorem cos : GlobalTheory.Published.StandardCosocleGL := PositivityTheory.Exh.standardCosocleGL_holds
/- English proof (translation)
The claim follows from `PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds`.
-/
theorem bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
/- English proof (translation)
The claim follows from `PositivityTheory.Prw.zelevinskyPolynomialRing_of bz PositivityTheory.RgGu.segmentRepresentation PositivityTheory.Groth.grothendieckRingPolynomial_holds`.
-/
theorem zel : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  PositivityTheory.Prw.zelevinskyPolynomialRing_of bz PositivityTheory.RgGu.segmentRepresentation PositivityTheory.Groth.grothendieckRingPolynomial_holds
/- English proof (translation)
The claim follows from `PositivityTheory.Pf1.LocalLanglands.LDual.langlandsDataDualGL_of_cosocle cos`.
-/
theorem dual : GlobalTheory.Published.LanglandsDataDualGL := PositivityTheory.Pf1.LocalLanglands.LDual.langlandsDataDualGL_of_cosocle cos
/- English proof (translation)
The claim follows from `PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top`.
-/
theorem adm : GlobalTheory.Published.IrreducibleAdmissibleGL := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
/- English proof (translation)
The claim follows from `GlobalTheory.SmGL.depthZeroSupport`.
-/
theorem dzs : GlobalTheory.Published.DepthZeroSupport := GlobalTheory.SmGL.depthZeroSupport

end UpperTheory.Zero.LLC.Pr
