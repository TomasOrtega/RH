import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompact
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZPsiPG.exists_Qp_mul_KO` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIwasawaDecompParabolicMaximalCompact.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.iwasawa_decomp_parabolic_maximal_compact : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (g : GL (Fin (i + t)) k), ∃ q : Qp k i t, ∃ κ ∈ GlobalTheory.SplitWeil.KO k (Fin (i + t)), g = (q : GL (Fin (i + t)) k) * κ := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.exists_Qp_mul_KO | exact GlobalTheory.CompanionTheory.BZPsiPG.exists_Qp_mul_KO | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.exists_Qp_mul_KO <;> assumption)
