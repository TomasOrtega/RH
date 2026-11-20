import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSegmentRepresentation
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.IrreducibleAdmissibleGL

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL in
/- English proof (translation)
Introduce `Δ` and use `GlobalTheory.CompanionTheory.SegExists.exists_isLSeg PositivityTheory.Exh.irreducibleAdmissibleGL Δ`.
-/
theorem PositivityTheory.Exh.lSegExists (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Zc.LSegExists k := fun Δ => GlobalTheory.CompanionTheory.SegExists.exists_isLSeg PositivityTheory.Exh.irreducibleAdmissibleGL Δ
