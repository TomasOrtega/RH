import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

/- English proof (translation)
Set `L : MvPolynomial σ k →ₗ[k] k` to `(MvPolynomial.basisMonomials σ k).constr k w`. Establish `hL : ∀ (m : σ →₀ ℕ) (a : k), L (MvPolynomial.monomial m a) = a * w m`. Introduce `m a`. Establish `h1 : (MvPolynomial.monomial m a : MvPolynomial σ k) = a • MvPolynomial.basisMonomials σ k m`. Rewrite using `[MvPolynomial.coe_basisMonomials]`.

Simplify using `[MvPolynomial.smul_monomial]`. Rewrite using `[h1, map_smul, Module.Basis.constr_basis, smul_eq_mul]`. Establish `hP : ∀ P : MvPolynomial σ k, L P = ∑ mo ∈ P.support, P.coeff mo * w mo`. Introduce `P`. Use `conv_lhs => rw [P.as_sum]`.

Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun m _ => hL m _`. Rewrite using `[← hP]`. Use `conv_lhs => rw [P₁.as_sum, P₂.as_sum]`. Rewrite using `[Finset.sum_mul_sum, map_sum]`.

Use `Finset.sum_congr rfl fun m₁ _ => ?_` and prove the remaining obligations. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun m₂ _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.monomial_mul, hL]`.
-/
theorem sum_coeff_mul_weight {k σ : Type} [CommRing k] (w : (σ →₀ ℕ) → k) (P₁ P₂ : MvPolynomial σ k) :
    ∑ mo ∈ (P₁ * P₂).support, (P₁ * P₂).coeff mo * w mo =
      ∑ m₁ ∈ P₁.support, ∑ m₂ ∈ P₂.support, P₁.coeff m₁ * P₂.coeff m₂ * w (m₁ + m₂) := by
  let L : MvPolynomial σ k →ₗ[k] k := (MvPolynomial.basisMonomials σ k).constr k w
  have hL : ∀ (m : σ →₀ ℕ) (a : k), L (MvPolynomial.monomial m a) = a * w m := by
    intro m a
    have h1 : (MvPolynomial.monomial m a : MvPolynomial σ k) =
        a • MvPolynomial.basisMonomials σ k m := by
      rw [MvPolynomial.coe_basisMonomials]
      simp [MvPolynomial.smul_monomial]
    rw [h1, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  have hP : ∀ P : MvPolynomial σ k, L P = ∑ mo ∈ P.support, P.coeff mo * w mo := by
    intro P
    conv_lhs => rw [P.as_sum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => hL m _
  rw [← hP]
  conv_lhs => rw [P₁.as_sum, P₂.as_sum]
  rw [Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  rw [MvPolynomial.monomial_mul, hL]

/- English proof (translation)
Introduce `k _ ι _ n mu T P₁ P₂ h₁ h₂`. Rewrite using `[sum_coeff_mul_weight (fun mo => ∏ b, mu b (colM mo b)) P₁ P₂, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ => ?_` and prove the remaining obligations. Establish `e₁ : ∏ b ∈ T, mu b (colM (m₁ + m₂) b) = ∏ b ∈ T, mu b (colM m₁ b)`. Use `Finset.prod_congr rfl fun b hb => ?_` and prove the remaining obligations.

Use `congr 1`. Use extensionality with `l`. Establish `: m₂ (l, b) = 0`. Assume the negation of the conclusion as `h`. Conclude with `h₂ m₂ hm₂ l b h hb`.

Simplify using `[colM, this]`. Establish `e₂ : ∏ b ∈ Tᶜ, mu b (colM (m₁ + m₂) b) = ∏ b ∈ Tᶜ, mu b (colM m₂ b)`. Use `Finset.prod_congr rfl fun b hb => ?_` and prove the remaining obligations. Use `congr 1`. Use extensionality with `l`.

Establish `: m₁ (l, b) = 0`. Assume the negation of the conclusion as `h`. Conclude with `(Finset.mem_compl.1 hb) (h₁ m₁ hm₁ l b h)`. Simplify using `[colM, this]`. Rewrite using `[← Finset.prod_mul_prod_compl T, e₁, e₂]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem colValue_mul_of_disjoint_columns :
    ∀ (k : Type) [CommRing k] (ι : Type) [Fintype ι] (n : ℕ) (mu : Fin n → (ι →₀ ℕ) → k) (T : Finset (Fin n)) (P₁ P₂ : MvPolynomial (ι × Fin n) k), (∀ mo ∈ P₁.support, ∀ l b, mo (l, b) ≠ 0 → b ∈ T) → (∀ mo ∈ P₂.support, ∀ l b, mo (l, b) ≠ 0 → b ∉ T) → ∑ mo ∈ (P₁ * P₂).support, (P₁ * P₂).coeff mo * ∏ b, mu b (colM mo b) = (∑ mo ∈ P₁.support, P₁.coeff mo * ∏ b ∈ T, mu b (colM mo b)) * ∑ mo ∈ P₂.support, P₂.coeff mo * ∏ b ∈ Tᶜ, mu b (colM mo b) := by
  intro k _ ι _ n mu T P₁ P₂ h₁ h₂
  rw [sum_coeff_mul_weight (fun mo => ∏ b, mu b (colM mo b)) P₁ P₂, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m₁ hm₁ => Finset.sum_congr rfl fun m₂ hm₂ => ?_
  have e₁ : ∏ b ∈ T, mu b (colM (m₁ + m₂) b) = ∏ b ∈ T, mu b (colM m₁ b) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    congr 1
    ext l
    have : m₂ (l, b) = 0 := by
      by_contra h
      exact h₂ m₂ hm₂ l b h hb
    simp [colM, this]
  have e₂ : ∏ b ∈ Tᶜ, mu b (colM (m₁ + m₂) b) = ∏ b ∈ Tᶜ, mu b (colM m₂ b) := by
    refine Finset.prod_congr rfl fun b hb => ?_
    congr 1
    ext l
    have : m₁ (l, b) = 0 := by
      by_contra h
      exact (Finset.mem_compl.1 hb) (h₁ m₁ hm₁ l b h)
    simp [colM, this]
  rw [← Finset.prod_mul_prod_compl T, e₁, e₂]
  ring

end GlobalTheory
