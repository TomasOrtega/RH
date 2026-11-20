import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.WeilBound.CoreStatements.ComplexPeriods.FlatDegreeResidues.FlatSlim
import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResK
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatDegreeHypotheses

section
/- English proof (translation)
Introduce `_ _ _` and use `FlatDegreeResidue.flatDegreeSt_of_resK PositivityTheory.ResPlug.FromRes.resK`.
-/
theorem UpperTheory.Lit.Flat.flat_tensor_swap_isIso : _root_.GlobalTheory.T.FlatDegreeHypotheses :=
  fun _ _ _ => FlatDegreeResidue.flatDegreeSt_of_resK PositivityTheory.ResPlug.FromRes.resK
end
