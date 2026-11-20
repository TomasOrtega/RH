import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistInjective
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FCuspidalTwistInjective.lean&line=130#L130)
-/
theorem _root_.GlobalTheory.T.cuspidal_twist_injective : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL k) (hx : x.IsCusp) (a b : ℕ) (h : x.nu (a : ℂ) = x.nu (b : ℂ)), a = b := by
  first | exact @GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj | exact GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj | (intros; apply GlobalTheory.CompanionTheory.SegNu.nu_natCast_inj <;> assumption)
