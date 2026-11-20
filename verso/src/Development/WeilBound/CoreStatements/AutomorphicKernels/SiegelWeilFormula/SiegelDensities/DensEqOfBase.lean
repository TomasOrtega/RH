import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.DensEqOfPieces
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.OneVecBinary
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.MassTop

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

/- English proof (translation)
The claim follows from `densEq_of_pieces PositivityTheory.Rg.Mass.oneVecBinary PositivityTheory.PfSWUS.HMass.oneVecBinaryMass hB hBase hO`.
-/
theorem densEq_of_base (hB : PositivityTheory.PfSWUS.HMass.SchwartzDensInf) (hBase : BaseOne) (hO : MassOne) :
    PositivityTheory.SiegelWeilFormula.Gen.DensEq :=
  densEq_of_pieces PositivityTheory.Rg.Mass.oneVecBinary PositivityTheory.PfSWUS.HMass.oneVecBinaryMass hB hBase hO

end PositivityTheory.SiegelWeilFormula.Densx

end
