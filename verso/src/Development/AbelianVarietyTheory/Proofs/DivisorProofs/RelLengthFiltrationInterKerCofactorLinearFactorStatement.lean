import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelLengthFiltrationInterKerCofactorLinearFactor
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelLengthFiltrationInterKerCofactorLinearFactor.lean&line=258#L258)
-/
theorem _root_.GlobalTheory.T.relLength_filtrationInterKerCofactor_linearFactor : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (S : Type) [Fintype S] [DecidableEq S] (a : S → Int0 v), Function.Injective a → ∀ (N : ℕ) (Fil : Submodule (RS a) (Fin N → RS a)), (∀ (c : Int0 v) (x : Fin N → RS a), c ≠ 0 → c • x ∈ Fil → x ∈ Fil) → ∀ τ : S, ∃ r : ℝ, (r : WithTop ℝ) = yExp v a Fil τ ∧ RelLen v ((filKer a Fil τ).map (mulR a N (lin a τ))) (filKer a Fil τ) r := by
  first | exact @GlobalTheory.HerbCore.relLen_lin_filKer | exact GlobalTheory.HerbCore.relLen_lin_filKer | (intros; apply GlobalTheory.HerbCore.relLen_lin_filKer <;> assumption)
