import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.LUnlinkedIrrOfHeredity
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.CuspPairIrr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports

noncomputable section

namespace GlobalTheory.RgGu.Unl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Treat this case separately. Treat this case separately. Treat this case separately.

A detailed English derivation is pending.
-/
theorem lUnlinkedIrr_pole (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GlobalTheory.BZSeg.LUnlinkedIrr k := by
  intro k _ _ _ _
  have hA : GlobalTheory.Published.IrreducibleAdmissibleGL := by
    first
    | exact PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
    | exact PositivityTheory.Exh.irreducibleAdmissibleGL
    | exact GlobalTheory.RgGu.irreducibleAdmissibleGL
  exact lUnlinkedIrr_nu k (GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ)
    PositivityTheory.Geo.geometricLemmaFiltration (PositivityTheory.RgGu.NR.nuPair k)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem lUnlinkedComm_pole (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GlobalTheory.BZSeg.LUnlinkedComm k :=
  fun k _ _ _ _ => lUnlinkedComm_of_irr k (lUnlinkedIrr_pole hZ k)

end GlobalTheory.RgGu.Unl

end
