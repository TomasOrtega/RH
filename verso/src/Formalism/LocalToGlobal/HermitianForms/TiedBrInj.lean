import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

noncomputable section

namespace Formalism.L2.Forms

open MvPolynomial

variable {ι : Type} [Fintype ι] {n : ℕ}

def detAll (ι : Type) [Fintype ι] (n : ℕ) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  ∏ τ, rename (fun ab : Fin n × Fin n => (τ, ab)) (Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).det

/- English proof (translation)
Unfold `detAll`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval_rename, RingHom.map_det]`. Use `congr 1`.

Use extensionality with `a b`. Simplify using `[Matrix.mvPolynomialX]`.
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
Introduce `h`. Establish `e` using `congrArg (MvPolynomial.eval (fun p : ι × Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) ℂ) p.2.1 p.2.2)) h`. Rewrite `e` using `[eval_detAll, map_zero]`. Establish `e3 : ∀ τ : ι, (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b).det = 1` using `fun τ => by`. Establish `h1 : (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b) = 1` using `by ext a b; rfl`.

Rewrite using `[h1, Matrix.det_one]`. Establish `e4 : (∏ τ : ι, (Matrix.of fun a b => (1 : Matrix (Fin n) (Fin n) ℂ) a b).det) = 1` using `Finset.prod_eq_one fun τ _ => e3 τ`. Conclude with `one_ne_zero (e4.symm.trans e)`.
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
Establish `h2 : P * detAll ι n = 0`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[map_mul, eval_detAll, map_zero]`. Distinguish the cases in `hx : ∀ τ, IsUnit (Matrix.of fun a b => x (τ, a, b)).det`.

Rewrite using `[h x hx, zero_mul]`. Use `push_neg at hx`. Take `⟨τ, hτ⟩` from `hx`. Rewrite `hτ` using `[isUnit_iff_ne_zero, not_not]`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ τ) hτ, mul_zero]`.

Conclude with `(mul_eq_zero.1 h2).resolve_right detAll_ne_zero`.
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
Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `P hP`. Apply `eq_zero_of_eval_units P` to reduce the goal to its premises. Introduce `x hx`. Set `X : ι → Matrix (Fin n) (Fin n) ℂ` to `fun τ => Matrix.of fun a b => x (τ, a, b)`.

Establish `hy : ∀ τ, IsUnit ((M τ)⁻¹ * X τ).det` using `fun τ => by`. Rewrite using `[Matrix.det_mul]`. Conclude with `(Matrix.isUnit_nonsing_inv_det _ (hM τ)).mul (hx τ)`. Set `y : Frames G` to `⟨fun τ => (M τ)⁻¹ * X τ, hy⟩`. Establish `hMy : ∀ τ, M τ * y.1 τ = X τ` using `fun τ => Matrix.mul_nonsing_inv_cancel_left _ _ (hM τ)`.

Establish `e` using `congrFun hP y`. Simplify using `only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, hMy] at e`. Establish `hprod : (∏ τ, (X τ).det ^ s τ) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ (hx τ).ne_zero`. Establish `e2` using `(mul_eq_zero.1 e).resolve_left hprod`. Simplify `e2` using `[X]`.
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
