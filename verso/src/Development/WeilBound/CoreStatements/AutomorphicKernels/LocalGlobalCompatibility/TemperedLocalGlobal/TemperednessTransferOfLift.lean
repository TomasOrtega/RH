import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.Bridge
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistenceOfSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationsOfExistenceOfSubgroupStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationSymmetryStatement
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationOperations
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelationInequalityAbelianStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedRestrictionStatement

namespace LocalGlobalAboveLAlt

/- English proof (translation)
The claim follows from `GlobalTheory.T.existence_of_subgroup`.
-/
theorem exSub : ExSub := GlobalTheory.T.existence_of_subgroup
/- English proof (translation)
The claim follows from `GlobalTheory.T.relations_of_existence_of_subgroup exSub`.
-/
theorem relOfMain : RelOfMain := GlobalTheory.T.relations_of_existence_of_subgroup exSub
/- English proof (translation)
The claim follows from `GlobalTheory.T.relation_symmetry`.
-/
theorem relSymm : RelSymm := GlobalTheory.T.relation_symmetry
/- English proof (translation)
The claim follows from `GlobalTheory.T.relation_inequality_abelian`.
-/
theorem relIneAb : RelIneAb := GlobalTheory.T.relation_inequality_abelian
/- English proof (translation)
The claim follows from `GlobalTheory.T.tempered_restriction`.
-/
theorem tempRes : TempRes := GlobalTheory.T.tempered_restriction

/- English proof (translation)
The claim follows from `local_global_of_iwahori relOfMain (PositivityTheory.Pf1.CLGD.Bridge.iwahori_compatibility_of_chains H)`.
-/
theorem local_global_of_lift (H : PositivityTheory.Pf1.CLGD.K.Main) : LocalGlobalSubnormal :=
  local_global_of_iwahori relOfMain (PositivityTheory.Pf1.CLGD.Bridge.iwahori_compatibility_of_chains H)

/- English proof (translation)
The claim follows from `PositivityTheory.Pf1.CLGD.Bridge.temperedness_of_restriction H exSub tempRes`.
-/
theorem temperedness_transfer_of_lift (H : PositivityTheory.Pf1.CLGD.K.Main) : TemperednessTransfer :=
  PositivityTheory.Pf1.CLGD.Bridge.temperedness_of_restriction H exSub tempRes

end LocalGlobalAboveLAlt
