import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfThree
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.EmbeddingMiddleFactorTriple
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LUnlinkedIrrOfSeg

namespace PositivityTheory.Exh

/- English proof (translation)
The claim follows from `standardCosocle_of hZ (lUnlinkedIrr_of_seg hZ)`.
-/
theorem standardCosocleGL_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.StandardCosocleGL :=
  standardCosocle_of hZ (lUnlinkedIrr_of_seg hZ)

/- English proof (translation)
Establish `hU` using `lUnlinkedIrr_of_seg hZ`. Conclude with `exhaustion_of_three hZ hU fun k _ _ _ _ => ⟨midP' k irreducibleAdmissibleGL, refineP' k, swapP' k (GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm k irreducibleAdmissibleGL (hU k))⟩`.
-/
theorem langlandsExhaustionGL_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.LanglandsExhaustionGL := by
  have hU := lUnlinkedIrr_of_seg hZ
  exact exhaustion_of_three hZ hU fun k _ _ _ _ =>
    ⟨midP' k irreducibleAdmissibleGL, refineP' k,
      swapP' k (GlobalTheory.CompanionTheory.BZSegComm.lUnlinkedComm k irreducibleAdmissibleGL (hU k))⟩

/- English proof (translation)
The claim follows from `multisegments_of hZ (lUnlinkedIrr_of_seg hZ) (langlandsExhaustionGL_of_seg hZ)`.
-/
theorem langlandsMultisegments_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.LanglandsMultisegments :=
  multisegments_of hZ (lUnlinkedIrr_of_seg hZ) (langlandsExhaustionGL_of_seg hZ)

end PositivityTheory.Exh
