import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistProductDistributes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsingletonOfGiso
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibOrd
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FTwistProductDistributes.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.twist_product_distributes : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (A : GRep k r) (B : GRep k t) (s : ℝ), GIso ((A.prod B).tw s) ((A.tw s).prod (B.tw s)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibOrd.giso_tw_prod | exact GlobalTheory.CompanionTheory.LeibOrd.giso_tw_prod | (intros; apply GlobalTheory.CompanionTheory.LeibOrd.giso_tw_prod <;> assumption)
