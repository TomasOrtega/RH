import Mathlib

set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.DomainDens

def blockSym {ι : Type} {p q n : ℕ} [Fintype ι] (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι) :
    Matrix (Fin p) (Fin p) (MvPolynomial (Fin n × Fin n) ℂ) :=
  Matrix.of fun i j => ∑ b : Fin q,
    X (Fintype.equivFinOfCardEq h (τ, i, b), Fintype.equivFinOfCardEq h (τ, j, b))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blockSym_apply {ι : Type} {p q n : ℕ} [Fintype ι] (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι)
    (i j : Fin p) : blockSym h τ i j =
      ∑ b : Fin q, X (Fintype.equivFinOfCardEq h (τ, i, b), Fintype.equivFinOfCardEq h (τ, j, b)) := rfl

/- English proof (translation)
Simplify using `[blockSym, Subsingleton.elim (Fintype.equivFinOfCardEq _ _) 0]`.
-/
example : blockSym (ι := Unit) (p := 1) (q := 1) (n := 1) (by simp) () 0 0 = X (0, 0) := by
  simp [blockSym, Subsingleton.elim (Fintype.equivFinOfCardEq _ _) 0]

end GlobalTheory.DomainDens
