import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.UnlinkedIrreducibility.LUnlinkedIrrOfHeredity
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.CuspPairIrr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports

noncomputable section

namespace GlobalTheory.RgGu.Unl

/- English proof (translation)
Introduce `k _ _ _ _`. Establish `hA : GlobalTheory.Published.IrreducibleAdmissibleGL` using `by first`. Consider the case `exact PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top`. Consider the case `exact PositivityTheory.Exh.irreducibleAdmissibleGL`. Consider the case `exact GlobalTheory.RgGu.irreducibleAdmissibleGL`.

Conclude with `lUnlinkedIrr_nu k (GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hA hZ) PositivityTheory.Geo.geometricLemmaFiltration (PositivityTheory.RgGu.NR.nuPair k)`.
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
Introduce `k _ _ _ _` and use `lUnlinkedComm_of_irr k (lUnlinkedIrr_pole hZ k)`.
-/
theorem lUnlinkedComm_pole (hZ : GlobalTheory.Published.SegmentRepresentation) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      GlobalTheory.BZSeg.LUnlinkedComm k :=
  fun k _ _ _ _ => lUnlinkedComm_of_irr k (lUnlinkedIrr_pole hZ k)

end GlobalTheory.RgGu.Unl

end
