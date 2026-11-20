import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenRight
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.HeckeJacquet.hecke_omega_jacquet` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHeckeOperatorJacquetEigenRight.lean&line=255#L255)
-/
theorem _root_.GlobalTheory.T.hecke_operator_jacquet_eigen_right : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ m : ℕ, 1 ≤ m → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ T : Module.End ℂ (fixed π (Zls.Km k N m)), Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N (d 0))) T → ∀ v : fixed π (Zls.Km k N m), (Submodule.Quotient.mk ((T v : fixed π (Zls.Km k N m)) : V) : Jacquet π (unipRad k (stdBlocks d hd))) = Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) (v : V)) := by
  first | exact @GlobalTheory.CompanionTheory.HeckeJacquet.hecke_omega_jacquet | exact GlobalTheory.CompanionTheory.HeckeJacquet.hecke_omega_jacquet | (intros; apply GlobalTheory.CompanionTheory.HeckeJacquet.hecke_omega_jacquet <;> assumption)
