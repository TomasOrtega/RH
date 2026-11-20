import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosocleSurjectionFactor
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCosocleSurjectionFactor.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.cosocle_surjection_factor : ∀ {G V W X : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (σ : Representation ℂ G W) (P : Representation ℂ G V) (Q : Representation ℂ G X) (hc : IsCosocle σ P) (hfl : HasFiniteLength P) (f : P.IntertwiningMap Q) (hf : Function.Surjective f) (hQ : Nontrivial X), ∃ g : Q.IntertwiningMap σ, Function.Surjective g := by
  first | exact @GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient | exact GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient | (intros; apply GlobalTheory.CompanionTheory.Segments.cosocle_quotient_of_quotient <;> assumption)
