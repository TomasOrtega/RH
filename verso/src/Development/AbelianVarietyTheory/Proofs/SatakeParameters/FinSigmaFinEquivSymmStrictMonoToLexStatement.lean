import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLex
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FFinSigmaFinEquivSymmStrictMonoToLex.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex : ∀ (s : ℕ) (t : Fin s → ℕ), StrictMono fun c : Fin (∑ a, t a) => (toLex (finSigmaFinEquiv.symm c) : Σₗ a, Fin (t a)) := by
  first | exact @GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex | exact GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex | (intros; apply GlobalTheory.finSigmaFinEquiv_symm_strictMono_lex <;> assumption)
