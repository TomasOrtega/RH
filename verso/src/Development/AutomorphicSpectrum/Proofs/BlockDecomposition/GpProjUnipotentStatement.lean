import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjUnipotent
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GpUnip.gpProj_unip` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FGpProjUnipotent.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.gpProj_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (u : MirabolicParabolic k m j), (u : Mir k (m + j)) ∈ MirUin k (m + j) → (gpProj k m j u).1 = 1 ∧ (gpProj k m j u).2 ∈ MirUin k j := by
  first | exact @GlobalTheory.CompanionTheory.GpUnip.gpProj_unip | exact GlobalTheory.CompanionTheory.GpUnip.gpProj_unip | (intros; apply GlobalTheory.CompanionTheory.GpUnip.gpProj_unip <;> assumption)
