import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothOfThree
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LUnlinkedIrrOfSeg
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.EmbeddingMiddleFactorTriple

namespace PositivityTheory.Groth

/- English proof (translation)
Establish `hu` using `Exh.lUnlinkedIrr_of_seg hZ`. Use `groth_of_three hZ (fun k _ _ _ _ => hu k) (fun k _ _ _ _ => ?_)` and prove the remaining obligations. Conclude with `⟨Exh.midP' k Exh.irreducibleAdmissibleGL, Exh.refineP' k, Exh.swapP' k (ClsOfF.comm_of (hu k))⟩`.
-/
theorem grothendieckRingPolynomial_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.GrothendieckRingPolynomial := by
  have hu := Exh.lUnlinkedIrr_of_seg hZ
  refine groth_of_three hZ (fun k _ _ _ _ => hu k) (fun k _ _ _ _ => ?_)
  exact ⟨Exh.midP' k Exh.irreducibleAdmissibleGL, Exh.refineP' k,
    Exh.swapP' k (ClsOfF.comm_of (hu k))⟩

end PositivityTheory.Groth
