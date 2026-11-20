import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiPgCommutationHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZPhiPG.phiPG` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPhiPgCommutationHolds.lean&line=231#L231)
-/
theorem _root_.GlobalTheory.T.phi_pg_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG k := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.phiPG | exact GlobalTheory.CompanionTheory.BZPhiPG.phiPG | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.phiPG <;> assumption)
