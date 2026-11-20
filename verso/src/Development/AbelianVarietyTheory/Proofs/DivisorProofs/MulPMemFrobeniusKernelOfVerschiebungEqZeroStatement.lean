import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.mulP_mem_kerIdeal_of_verschiebung_eq_zero` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMulPMemFrobeniusKernelOfVerschiebungEqZero.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0) (G : PDivGroup p R) (a : G.A 1), (verschiebung h G).app 1 a = 0 → G.mulP 1 a ∈ kerIdeal ((G.mulP 1).comp ((relFrob h G).app 1)) := by
  first | exact @GlobalTheory.PDivGroup.mulP_mem_kerIdeal_of_verschiebung_eq_zero | exact GlobalTheory.PDivGroup.mulP_mem_kerIdeal_of_verschiebung_eq_zero | (intros; apply GlobalTheory.PDivGroup.mulP_mem_kerIdeal_of_verschiebung_eq_zero <;> assumption)
