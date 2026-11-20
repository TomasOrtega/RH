import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylConjParabolicProj
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWeylConjParabolicProj.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.weyl_conj_parabolic_proj : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (h : HPG k i (t + 1)),
  ∃ hη : wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ ∈ HPG k (i + 1) (t + 1),
    pgProj k (i + 1) (t + 1) ⟨_, hη⟩ = (sEmb k i (pgProj k i (t + 1) h).1, (pgProj k i (t + 1) h).2) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.EtaConj.eta_mem_proj | exact GlobalTheory.CompanionTheory.BZPhiPG.EtaConj.eta_mem_proj | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.EtaConj.eta_mem_proj <;> assumption)
