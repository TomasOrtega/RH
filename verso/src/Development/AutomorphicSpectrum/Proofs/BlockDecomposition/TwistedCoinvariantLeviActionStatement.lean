import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCoinvariantLeviAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistedCoinvariantLeviAction.lean&line=49#L49)
-/
theorem _root_.GlobalTheory.T.twisted_coinvariant_levi_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (a : Mir k i) (w : GL (Fin (t + 1)) k) (v : τ.V ⊗[ℂ] σ.V),
  qO τ σ ψ (extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (sEmb k i a, w) v) =
    (((dpowM i (1 / 2) a : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w : ℂˣ) : ℂ)) •
      extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a, w) (qO τ σ ψ v) := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Coinv.intertwine | exact GlobalTheory.CompanionTheory.BZPhiPG.Coinv.intertwine | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Coinv.intertwine <;> assumption)
