import Mathlib
open MvPolynomial

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [optionEquivLeft_C]`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p i hp`. Break down `i with _ | j` into its components or cases.

Simplify using `[Derivation.leibniz, hp, optionEquivLeft_X_none, mul_comm]`. Simplify using `[Derivation.leibniz, hp, optionEquivLeft_X_some, pderiv_X, mul_comm]`.
-/
theorem optionEquivLeft_pderiv_none_gen {τ : Type} [DecidableEq τ]
    (p : MvPolynomial (Option τ) ℂ) :
    optionEquivLeft ℂ τ (pderiv none p) = Polynomial.derivative (optionEquivLeft ℂ τ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [optionEquivLeft_C]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rcases i with _ | j
    · simp [Derivation.leibniz, hp, optionEquivLeft_X_none, mul_comm]
    · simp [Derivation.leibniz, hp, optionEquivLeft_X_some, pderiv_X, mul_comm]

/- English proof (translation)
Introduce `τ _ k s`. Rewrite using `[optionEquivLeft_pderiv_none_gen, Polynomial.coeff_derivative, MvPolynomial.smul_eq_C_mul, mul_comm]`. Use `congr 1`. Simplify using the standard rewrite rules.
-/
theorem optionEquivLeft_pderiv_none_coeff :
    ∀ {τ : Type} [DecidableEq τ] (k : ℕ) (s : MvPolynomial (Option τ) ℂ),
      (MvPolynomial.optionEquivLeft ℂ τ (MvPolynomial.pderiv none s)).coeff k =
        ((k : ℂ) + 1) • (MvPolynomial.optionEquivLeft ℂ τ (s)).coeff (k + 1) := by
  intro τ _ k s
  rw [optionEquivLeft_pderiv_none_gen, Polynomial.coeff_derivative, MvPolynomial.smul_eq_C_mul,
    mul_comm]
  congr 1
  simp

end GlobalTheory
