import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

noncomputable section

namespace Formalism.L2.Forms

open MvPolynomial

variable {ι : Type} [Fintype ι] {n : ℕ}

def detAll (ι : Type) [Fintype ι] (n : ℕ) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  ∏ τ, rename (fun ab : Fin n × Fin n => (τ, ab)) (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem eval_detAll (x : ι × Fin n × Fin n → ℂ) :
    eval x (detAll ι n) = ∏ τ, (Matrix.of fun a b => x (τ, a, b)).det := by
  unfold detAll
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.eval_rename, RingHom.map_det]
  congr 1
  ext a b
  simp [Matrix.mvPolynomialX]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem detAll_ne_zero : detAll ι n ≠ 0 := by
  intro h
  have e := congrArg (MvPolynomial.eval (fun p : ι × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) p.2.1 p.2.2)) h
  rw [eval_detAll, map_zero] at e
  have e3 : ∀ τ : ι, (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b).det = 1 := fun τ => by
    have h1 : (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b) = 1 := by ext a b; rfl
    rw [h1, Matrix.det_one]
  have e4 : (∏ τ : ι, (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b).det) = 1 :=
    Finset.prod_eq_one fun τ _ => e3 τ
  exact one_ne_zero (e4.symm.trans e)

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem eq_zero_of_eval_units (P : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (h : ∀ x : ι × Fin n × Fin n → ℂ, (∀ τ, IsUnit (Matrix.of fun a b => x (τ, a, b)).det) → eval x P = 0) : P = 0 := by
  have h2 : P * detAll ι n = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, eval_detAll, map_zero]
    by_cases hx : ∀ τ, IsUnit (Matrix.of fun a b => x (τ, a, b)).det
    · rw [h x hx, zero_mul]
    · push_neg at hx
      obtain ⟨τ, hτ⟩ := hx
      rw [isUnit_iff_ne_zero, not_not] at hτ
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]
  exact (mul_eq_zero.1 h2).resolve_right detAll_ne_zero

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem fnOf_injective (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (M : ι → Matrix (Fin n) (Fin n) ℂ)
    (hM : ∀ τ, IsUnit (M τ).det) : Function.Injective (fnOf G s M) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro P hP
  apply eq_zero_of_eval_units P
  intro x hx
  let X : ι → Matrix (Fin n) (Fin n) ℂ := fun τ => Matrix.of fun a b => x (τ, a, b)
  have hy : ∀ τ, IsUnit ((M τ)⁻¹ * X τ).det := fun τ => by
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det _ (hM τ)).mul (hx τ)
  let y : Frames G := ⟨fun τ => (M τ)⁻¹ * X τ, hy⟩
  have hMy : ∀ τ, M τ * y.1 τ = X τ := fun τ => Matrix.mul_nonsing_inv_cancel_left _ _ (hM τ)
  have e := congrFun hP y
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hMy] at e
  have hprod : (∏ τ, (X τ).det ^ s τ) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hx τ).ne_zero
  have e2 := (mul_eq_zero.1 e).resolve_left hprod
  simpa [X] using e2

end Formalism.L2.Forms
