import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistTwistAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistTwistAdd.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.twist_twist_add : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : GRep k n) (s s' : ℝ), GIso ((A.tw s).tw s') (A.tw (s + s')) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.giso_tw_tw | exact GlobalTheory.CompanionTheory.LeibOrd.giso_tw_tw | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.giso_tw_tw <;> assumption)
