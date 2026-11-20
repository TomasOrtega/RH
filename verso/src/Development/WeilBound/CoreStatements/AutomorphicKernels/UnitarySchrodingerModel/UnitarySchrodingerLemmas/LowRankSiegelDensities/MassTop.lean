import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SharpCount

namespace PositivityTheory.PfSWUS.HMass

/- English proof (translation)
The claim follows from `oneVecBinaryMass_of sharpCount`.
-/
theorem oneVecBinaryMass : OneVecBinaryMass := oneVecBinaryMass_of sharpCount

/- English proof (translation)
The claim follows from `siegelDensitiesLowA_of hE1 oneVecBinaryMass hB`.
-/
theorem siegelDensitiesLowA_of_leaves (hE1 : OneVecBinary) (hB : SchwartzDensInf) : SiegelDensitiesLowA :=
  siegelDensitiesLowA_of hE1 oneVecBinaryMass hB

end PositivityTheory.PfSWUS.HMass
