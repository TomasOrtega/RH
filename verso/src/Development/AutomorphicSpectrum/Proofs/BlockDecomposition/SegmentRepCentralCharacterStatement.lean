import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentRepCentralCharacter
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSegmentRepCentralCharacter.lean&line=53#L53)
-/
theorem _root_.GlobalTheory.T.segment_rep_central_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Δ : Segment k) (y : IrrGL k), IsLSeg Δ y.rep → ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy Δ.first t c → Zl.ScalarBy y t (c ^ Δ.len * ((absPow k (((Δ.len * (Δ.len - 1) / 2 : ℕ) : ℂ)) (t ^ Δ.d) : ℂˣ) : ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg | exact GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg | (intros; apply GlobalTheory.CompanionTheory.ZlScalar.scalarBy_lseg <;> assumption)
