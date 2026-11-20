import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SquareIntegrableSingleSegment
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSquareIntegrableSingleSegment.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.square_integrable_single_segment : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSocleGL k → Zl.CasselmanNecSq k → Zc.LSegExists k → ∀ (𝔪 : Multiset (Segment k)) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), 1 ≤ N → IsSmooth π → π.IsIrreducible → IsSqIntCoeff π → IsL 𝔪 π → 𝔪.card = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one | exact GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one | (intros; apply GlobalTheory.CompanionTheory.SquareIntegrableSegments.card_eq_one <;> assumption)
