import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.HasCLMNbar
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2Isometry
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.UnipotentPartBlockMatrix
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocCellA
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Decomp
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LNe
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.AwayNZ

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
The claim follows from `opGen_of' unipTau leviTau wEx schOps hF`.
-/
theorem opGen_of (hF : FTfact) : OpGen := opGen_of' unipTau leviTau wEx schOps hF

/- English proof (translation)
The claim follows from `opCLM_of unipTau leviTau wEx schOps hF decomp lNe`.
-/
theorem opCLM_of' (hF : FTfact) : OpCLM := opCLM_of unipTau leviTau wEx schOps hF decomp lNe

/- English proof (translation)
The claim follows from `local_isometry_of_hypotheses unipTau leviTau wEx schOps hF decomp lNe planchLoc awayNZ`.
-/
theorem local_L2_isometry (hF : FTfact) : LocalL2Isometry :=
  local_isometry_of_hypotheses unipTau leviTau wEx schOps hF decomp lNe planchLoc awayNZ

end PositivityTheory.Rg.Sw.Glob
