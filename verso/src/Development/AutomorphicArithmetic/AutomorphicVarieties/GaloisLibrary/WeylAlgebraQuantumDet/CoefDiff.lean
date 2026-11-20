import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WeylAlgebraQuantumDet.IsTop
open Matrix UpperTheory.V.Weyl

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp only [MvPolynomial.eval_C]`. Use `fun_prop`. Consider the case `add p q hp hq => simp only [map_add]`. Conclude with `hp.add hq`.

Consider the case `mul_X p ab hp`. Simplify using `only [map_mul, MvPolynomial.eval_X]`. Conclude with `hp.mul (by fun_prop)`.
-/
private theorem UpperTheory.V.Weyl.differentiable_eval_polynomial_entries (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → Fin n → ℂ => MvPolynomial.eval (fun ab => x ab.1 ab.2) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.eval_C]; fun_prop
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p ab hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (by fun_prop)

/- English proof (translation)
Introduce `n Ξ i j`. Take `⟨p, hp⟩` from `Ξ.poly i j`. Establish `h : Ξ.coef i j = fun x : Fin n → Fin n → ℂ => MvPolynomial.eval (fun ab => x ab.1 ab.2) p`. Use function extensionality and compare the values at `x`. Conclude with `hp (Matrix.of x)`.

Rewrite using `[h]`. Conclude with `UpperTheory.V.Weyl.differentiable_eval_polynomial_entries n p`.
-/
theorem UpperTheory.V.Weyl.coefDiff :
    ∀ (n : ℕ) (Ξ : Pre n) (i j : Fin Ξ.d), Differentiable ℂ (Ξ.coef i j) := by
  intro n Ξ i j
  obtain ⟨p, hp⟩ := Ξ.poly i j
  have h : Ξ.coef i j = fun x : Fin n → Fin n → ℂ => MvPolynomial.eval (fun ab => x ab.1 ab.2) p := by
    funext x
    exact hp (Matrix.of x)
  rw [h]
  exact UpperTheory.V.Weyl.differentiable_eval_polynomial_entries n p
