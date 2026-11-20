import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CanonicalSegmentsReverseOrdered
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducibleStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCanonicalSegmentsReverseOrdered.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.canonical_segments_reverse_ordered : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h : ℕ} (Γ : Fin h → Segment k), IsCanon Γ → IsRevOrdered Γ := by
  first | exact @GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon | exact GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon | (intros; apply GlobalTheory.CompanionTheory.Canon.isRevOrdered_of_isCanon <;> assumption)
