import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjContinuous
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZMir.continuous_gpProj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGpProjContinuous.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.gpProj_continuous : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), Continuous (gpProj k m j) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.continuous_gpProj | exact GlobalTheory.CompanionTheory.BZMir.continuous_gpProj | (intros; apply GlobalTheory.CompanionTheory.BZMir.continuous_gpProj <;> assumption)
