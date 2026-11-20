import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.LanglandsDataDualGLOfCosocle
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.EssSquareIntegrableSegmentsHolds
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.ProvedMore
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesMore
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero

namespace UpperTheory.Zero.LLC.Pr

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exh : GlobalTheory.Published.LanglandsExhaustionGL := PositivityTheory.Exh.langlandsExhaustionGL_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem multi : GlobalTheory.Published.LanglandsMultisegments := PositivityTheory.Exh.langlandsMultisegments_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cos : GlobalTheory.Published.StandardCosocleGL := PositivityTheory.Exh.standardCosocleGL_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zel : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  PositivityTheory.Prw.zelevinskyPolynomialRing_of bz PositivityTheory.RgGu.segmentRepresentation PositivityTheory.Groth.grothendieckRingPolynomial_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dual : GlobalTheory.Published.LanglandsDataDualGL := PositivityTheory.Pf1.LocalLanglands.LDual.langlandsDataDualGL_of_cosocle cos
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem adm : GlobalTheory.Published.IrreducibleAdmissibleGL := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dzs : GlobalTheory.Published.DepthZeroSupport := GlobalTheory.SmGL.depthZeroSupport

end UpperTheory.Zero.LLC.Pr
