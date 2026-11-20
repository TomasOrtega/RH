import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HGPClosed
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHGPClosed.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.isClosed_mirabolicParabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), IsClosed (MirabolicParabolic k m j : Set (Mir k (m + j))) := by
  first | exact @GlobalTheory.CompanionTheory.MirGP.isClosed_HGP | exact GlobalTheory.CompanionTheory.MirGP.isClosed_HGP | (intros; apply GlobalTheory.CompanionTheory.MirGP.isClosed_HGP <;> assumption)
