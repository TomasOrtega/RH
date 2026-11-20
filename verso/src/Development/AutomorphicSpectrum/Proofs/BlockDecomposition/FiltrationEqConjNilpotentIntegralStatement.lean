import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationEqConjNilpotentIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagPairs
open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.IwJac.FiltTop.filt_top'` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFiltrationEqConjNilpotentIntegral.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.filtration_eq_conj_nilpotent_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ x : Fin n → ℤ, StrictAnti x → filt ϖ x n = (nO k n).map (MulAut.conj (tor ϖ x)).toMonoidHom := by
  first | exact @GlobalTheory.CompanionTheory.IwJac.FiltTop.filt_top' | exact GlobalTheory.CompanionTheory.IwJac.FiltTop.filt_top' | (intros; apply GlobalTheory.CompanionTheory.IwJac.FiltTop.filt_top' <;> assumption)
