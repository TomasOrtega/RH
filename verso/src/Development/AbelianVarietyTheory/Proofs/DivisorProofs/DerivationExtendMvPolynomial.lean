import Mathlib
open IsLocalRing TensorProduct

namespace GlobalTheory

open MvPolynomial in

noncomputable def coeffDerivFun {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p : MvPolynomial τ B) : MvPolynomial τ B :=
  ∑ s ∈ p.support, monomial s (D (coeff s p))

open MvPolynomial in
/- English proof (translation)
Rewrite using `[coeffDerivFun, coeff_sum]`. Simplify using `only [coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`. Both sides reduce to the same expression.

Rewrite using `[notMem_support_iff.mp h, map_zero]`.
-/
theorem coeff_coeffDerivFun {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p : MvPolynomial τ B) (m : τ →₀ ℕ) :
    coeff m (coeffDerivFun D p) = D (coeff m p) := by
  classical
  rw [coeffDerivFun, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

noncomputable def coeffDerivAddHom {B τ : Type} [CommRing B] (D : Derivation ℤ B B) :
    MvPolynomial τ B →+ MvPolynomial τ B where
  toFun := coeffDerivFun D
  map_zero' := by ext m; simp [coeff_coeffDerivFun]
  map_add' p q := by ext m; simp [coeff_coeffDerivFun]

/- English proof (translation)
Use extensionality with `m`. Express the relevant statement in the definitionally equal form `MvPolynomial.coeff m (coeffDerivFun D _) = _`. Rewrite using `[coeff_coeffDerivFun, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem coeffDerivAddHom_monomial {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (s : τ →₀ ℕ) (a : B) :
    coeffDerivAddHom D (MvPolynomial.monomial s a) = MvPolynomial.monomial s (D a) := by
  classical
  ext m
  change MvPolynomial.coeff m (coeffDerivFun D _) = _
  rw [coeff_coeffDerivFun, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  split_ifs <;> simp

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on' with`. Consider the case `monomial u a`. Proceed by induction on `q using MvPolynomial.induction_on' with`. Consider the case `monomial v b`. Simplify using `only [MvPolynomial.monomial_mul, coeffDerivAddHom_monomial, Derivation.leibniz, smul_eq_mul, map_add, add_comm v u]`.

Consider the case `add q₁ q₂ h₁ h₂`. Rewrite using `[mul_add, map_add, h₁, h₂, map_add]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `add p₁ p₂ h₁ h₂`. Rewrite using `[add_mul, map_add, h₁, h₂, map_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem coeffDerivAddHom_mul {B τ : Type} [CommRing B] (D : Derivation ℤ B B)
    (p q : MvPolynomial τ B) :
    coeffDerivAddHom D (p * q) = p * coeffDerivAddHom D q + q * coeffDerivAddHom D p := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    induction q using MvPolynomial.induction_on' with
    | monomial v b =>
      simp only [MvPolynomial.monomial_mul, coeffDerivAddHom_monomial, Derivation.leibniz,
        smul_eq_mul, map_add, add_comm v u]
    | add q₁ q₂ h₁ h₂ =>
      rw [mul_add, map_add, h₁, h₂, map_add]; ring
  | add p₁ p₂ h₁ h₂ =>
    rw [add_mul, map_add, h₁, h₂, map_add]; ring

/- English proof (translation)
Introduce `B τ _ D`. Use `⟨Derivation.mk' (coeffDerivAddHom D).toIntLinearMap (fun a b => by simpa [smul_eq_mul] using coeffDerivAddHom_mul D a b), ?_, ?_⟩` and prove the remaining obligations. Introduce `x show coeffDerivAddHom D (MvPolynomial.monomial 0 x) = MvPolynomial.monomial 0 (D x)`. Conclude with `coeffDerivAddHom_monomial D 0 x`. Introduce `t show coeffDerivAddHom D (MvPolynomial.monomial (Finsupp.single t 1) 1) = 0`.

Rewrite using `[coeffDerivAddHom_monomial, Derivation.map_one_eq_zero, map_zero]`.
-/
theorem derivation_extend_mvPolynomial :
    ∀ (B τ : Type) [CommRing B] (D : Derivation ℤ B B),
      ∃ D' : Derivation ℤ (MvPolynomial τ B) (MvPolynomial τ B),
        (∀ x, D' (MvPolynomial.C x) = MvPolynomial.C (D x)) ∧ ∀ t, D' (MvPolynomial.X t) = 0 := by
  intro B τ _ D
  refine ⟨Derivation.mk' (coeffDerivAddHom D).toIntLinearMap
    (fun a b => by simpa [smul_eq_mul] using coeffDerivAddHom_mul D a b), ?_, ?_⟩
  · intro x
    show coeffDerivAddHom D (MvPolynomial.monomial 0 x) = MvPolynomial.monomial 0 (D x)
    exact coeffDerivAddHom_monomial D 0 x
  · intro t
    show coeffDerivAddHom D (MvPolynomial.monomial (Finsupp.single t 1) 1) = 0
    rw [coeffDerivAddHom_monomial, Derivation.map_one_eq_zero, map_zero]

end GlobalTheory
