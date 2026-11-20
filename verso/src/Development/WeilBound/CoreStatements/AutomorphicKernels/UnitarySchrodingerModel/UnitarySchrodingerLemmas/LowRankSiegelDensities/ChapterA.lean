import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.MassTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.OneVecBinary

/- English proof (translation)
The claim follows from `PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA_of_leaves PositivityTheory.Rg.Mass.oneVecBinary hB`.
-/
theorem PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA_of_sch (hB : PositivityTheory.PfSWUS.HMass.SchwartzDensInf) :
    PositivityTheory.PfSWUS.HMass.SiegelDensitiesLowA :=
  PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA_of_leaves PositivityTheory.Rg.Mass.oneVecBinary hB
