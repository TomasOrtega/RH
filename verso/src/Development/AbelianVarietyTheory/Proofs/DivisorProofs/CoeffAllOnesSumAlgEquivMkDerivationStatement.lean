import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAllOnesSumAlgEquivMkDerivation
import Mathlib
open MvPolynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoeffAllOnesSumAlgEquivMkDerivation.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.coeff_allOnes_sumAlgEquiv_derivation_eq : ∀ {σ : Type} {L : ℕ} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (b : MvPolynomial (Fin L ⊕ σ) ℂ), MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (MvPolynomial.mkDerivation ℂ (Sum.elim (fun _ : Fin L => (0 : MvPolynomial (Fin L ⊕ σ) ℂ)) (fun v : σ => MvPolynomial.rename Sum.inr (D (MvPolynomial.X v)))) b)) = D (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (b))) := by
  first | exact @GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation | exact GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation | (intros; apply GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation <;> assumption)
