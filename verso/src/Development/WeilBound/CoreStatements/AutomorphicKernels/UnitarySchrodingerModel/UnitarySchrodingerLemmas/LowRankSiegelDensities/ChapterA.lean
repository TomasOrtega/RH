import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.MassTop
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.OneVecBinary

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA_of_sch (hB : PositivityTheory.PfSWUS.HMass.SchwartzDensInf) :
    PositivityTheory.PfSWUS.HMass.SiegelDensitiesLowA :=
  PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA_of_leaves PositivityTheory.Rg.Mass.oneVecBinary hB
