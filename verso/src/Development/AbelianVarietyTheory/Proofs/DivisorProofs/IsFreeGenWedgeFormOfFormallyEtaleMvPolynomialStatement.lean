import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomial
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopFormFrameBaseCoordinatesAddVariablesEtale
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsFreeGenWedgeFormOfFormallyEtaleMvPolynomial.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.isFreeGen_wedgeForm_of_formallyEtale_mvPolynomial : ∀ {k A₀ A : Type} [CommRing k] [CommRing A₀] [CommRing A] (α : k →+* A₀) (β : k →+* A)
    (ρ : A₀ →+* A), ρ.comp α = β → ∀ {n r : ℕ} (z : Fin n → A₀) (b : Module.Basis (Fin n) A₀ (Omega α)),
    (∀ i, b i = dFun α (z i)) → ∀ (t : Fin r → A), (MvPolynomial.eval₂Hom ρ t).FormallyEtale →
    IsFreeGen A (dForm β (Fin.append t (fun i => ρ (z i)))) := by
  first | exact @GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial | exact GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial | (intros; apply GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial <;> assumption)
