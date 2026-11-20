import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPairingLinearSubstitutionAdjoint
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetGNeZero
open Classical MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFockPairingLinearSubstitutionAdjoint.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.fockPairing_linearSubstitution_adjoint : ∀ {σ σ' : Type} [Fintype σ] [Fintype σ'] (M : Matrix σ' σ ℂ) (F : MvPolynomial σ ℂ) (F' : MvPolynomial σ' ℂ), Formalism.L2.DIV.fockS (GlobalTheory.MinorFrame.rsub M F) F' = Formalism.L2.DIV.fockS F (GlobalTheory.MinorFrame.rsub M.conjTranspose F') := by
  first | exact @GlobalTheory.MinorFrame.fockS_rsub_adj | exact GlobalTheory.MinorFrame.fockS_rsub_adj | (intros; apply GlobalTheory.MinorFrame.fockS_rsub_adj <;> assumption)
