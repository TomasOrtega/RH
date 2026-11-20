import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiBigTheorem.HSChain
import Development.WeilBound.CoreStatements.AutomorphicKernels.MoriwakiBigness.MoriwakiSymmetry.EqMapSymm
import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResK
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PoincareLelong.PoincareLelongInv
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelongStatement

namespace PositivityTheory.Pf1.HilbertSamuelMoriwaki

/- English proof (translation)
The claim follows from `moriwakiBig_of_classicalTheorems PositivityTheory.ResPlug.FromRes.resK (GlobalTheory.T.arith_intersection_system_of_poincare_lelong PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK) PositivityTheory.MbAis.DenseCurves.main`.
-/
theorem moriwakiBig_outright : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement :=
  moriwakiBig_of_classicalTheorems PositivityTheory.ResPlug.FromRes.resK
    (GlobalTheory.T.arith_intersection_system_of_poincare_lelong PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK) PositivityTheory.MbAis.DenseCurves.main

/- English proof (translation)
The claim follows from `hsUse_of_hypotheses PositivityTheory.ResPlug.FromRes.resK (GlobalTheory.T.arith_intersection_system_of_poincare_lelong PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK) PositivityTheory.MbAis.DenseCurves.main`.
-/
theorem hsUse_outright : HSUse :=
  hsUse_of_hypotheses PositivityTheory.ResPlug.FromRes.resK
    (GlobalTheory.T.arith_intersection_system_of_poincare_lelong PositivityTheory.Tls2.Pl.poincareLelong PositivityTheory.ResPlug.FromRes.resK) PositivityTheory.MbAis.DenseCurves.main

end PositivityTheory.Pf1.HilbertSamuelMoriwaki
