import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionUnipotentAction
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemTwKerIffAverage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentTopMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolicStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParabolicUnipotentLeviDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousLeviUnipotentProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothIntegralLinearChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompParabolicMaximalCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumOverCompactCosetsJacquetKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInducedSectionSupportedOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactCosetSet
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU.fibV_uM` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFibreFunctionUnipotentAction.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.fibre_function_unipotent_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W) (f : cIndSpace (HPG k i t) (hRep τ σ)) (y : Fin (i + t) → k) (κ : GL (Fin (i + t)) k) (v : Fin t → k), fibV (prodPG τ σ (uM k (i + t) y) f) κ v = topRep τ W (Multiplicative.ofAdd (topP i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) (fibV f κ (v + middlePart i t ((κ : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec y))) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU.fibV_uM | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU.fibV_uM | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.FibU.fibV_uM <;> assumption)
