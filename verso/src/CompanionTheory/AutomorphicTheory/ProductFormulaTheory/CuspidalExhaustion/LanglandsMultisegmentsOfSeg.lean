import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.ExhaustionOfThree
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.EmbeddingMiddleFactorTriple
import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.LUnlinkedIrrOfSeg

namespace CompanionTheory.Exh

/- English proof (translation)
The claim follows from `standardCosocle_of hZ (lUnlinkedIrr_of_seg hZ)`.
-/
theorem standardCosocleGL_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.StandardCosocleGL :=
  standardCosocle_of hZ (lUnlinkedIrr_of_seg hZ)

/- English proof (translation)
The claim follows from `exhaustion_of_three hZ (lUnlinkedIrr_of_seg hZ) fun k _ _ _ _ => ⟨midP' k irreducibleAdmissibleGL, refineP' k, swapP' k (GlobalTheory.T.unlinked_commute_of_irreducible k irreducibleAdmissibleGL (lUnlinkedIrr_of_seg hZ k))⟩`.
-/
theorem langlandsExhaustionGL_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.LanglandsExhaustionGL :=
  exhaustion_of_three hZ (lUnlinkedIrr_of_seg hZ) fun k _ _ _ _ =>
    ⟨midP' k irreducibleAdmissibleGL, refineP' k,
      swapP' k (GlobalTheory.T.unlinked_commute_of_irreducible k irreducibleAdmissibleGL (lUnlinkedIrr_of_seg hZ k))⟩

/- English proof (translation)
The claim follows from `multisegments_of hZ (lUnlinkedIrr_of_seg hZ) (langlandsExhaustionGL_of_seg hZ)`.
-/
theorem langlandsMultisegments_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.LanglandsMultisegments :=
  multisegments_of hZ (lUnlinkedIrr_of_seg hZ) (langlandsExhaustionGL_of_seg hZ)

end CompanionTheory.Exh
