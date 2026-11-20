import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiTensorIrreducibleNontrivial
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanCriterion.Zj
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FPiTensorIrreducibleNontrivial.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.pi_tensor_irreducible_nontrivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ {h : ℕ} (x : Fin h → IrrGL k), Nontrivial (PiTensorProduct ℂ (fun a => (x a).2.rep.V)) := by
  first | exact @GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL | exact GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL | (intros; apply GlobalTheory.CompanionTheory.TensorIrr.nontrivial_piTensorProduct_irrGL <;> assumption)
