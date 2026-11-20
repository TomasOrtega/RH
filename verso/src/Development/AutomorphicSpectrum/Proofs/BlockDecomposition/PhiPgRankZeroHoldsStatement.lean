import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgRankZeroHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.PhiPG0
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPhiPgRankZeroHolds.lean&line=645#L645)
-/
theorem _root_.GlobalTheory.T.phi_pg_rank_zero_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG0 k := by
  first | exact @GlobalTheory.CompanionTheory.MirLevi.phiPG0_holds | exact GlobalTheory.CompanionTheory.MirLevi.phiPG0_holds | (intros; apply GlobalTheory.CompanionTheory.MirLevi.phiPG0_holds <;> assumption)
