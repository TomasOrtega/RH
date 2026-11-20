import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DigitMonomialsBasisEnvelopeModPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FDigitMonomialsBasisEnvelopeModPow.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.digitMonomials_basis_envelope_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (J : Ideal A) (r : ℕ → MvPolynomial ℕ A), (∀ i, ∃ (v : Aˣ) (a b : MvPolynomial ℕ A), a ∈ MvPolynomial.supported A (Set.Iio i) ∧ b ∈ MvPolynomial.supported A (Set.Iio i) ∧ r i - (MvPolynomial.C (v : A) * MvPolynomial.X i ^ l + a * MvPolynomial.X i + b) ∈ J.map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) → ∀ n : ℕ, (∀ x : MvPolynomial ℕ A, ∃ c : Digits l →₀ A, x - c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A)) ∧ ∀ c : Digits l →₀ A, c.sum (fun α a => MvPolynomial.monomial α.1 a) ∈ Ideal.span (Set.range r) ⊔ (J ^ n).map (MvPolynomial.C : A →+* MvPolynomial ℕ A) → ∀ α, c α ∈ J ^ n := by
  first | exact @GlobalTheory.digitMonomials_basis_mod_pow | exact GlobalTheory.digitMonomials_basis_mod_pow | (intros; apply GlobalTheory.digitMonomials_basis_mod_pow <;> assumption)
