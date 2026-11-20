import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipotentLiftParabolicProj
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FExistsUnipotentLiftParabolicProj.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_unipotent_lift_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (n : MirUin k (j + 1)),
    ∃ (u : MirUin k (m + (j + 1))) (hh : (u : Mir k (m + (j + 1))) ∈ MirabolicParabolic k m (j + 1)),
      gpProj k m (j + 1) ⟨u, hh⟩ = (1, (n : Mir k (j + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift | exact GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.exists_mirUin_gpProj_lift <;> assumption)
