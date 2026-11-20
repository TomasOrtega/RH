import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiGpCommutationHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LeibPhi.phiGP` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPhiGpCommutationHolds.lean&line=319#L319)
-/
theorem _root_.GlobalTheory.T.phi_gp_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiGP k := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.phiGP | exact GlobalTheory.CompanionTheory.LeibPhi.phiGP | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.phiGP <;> assumption)
