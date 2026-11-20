import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

/- English proof (translation)
Unfold `polyAt`. Proceed by induction on `Δ using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p i hp`.

Rewrite using `[map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.aeval_X, MvPolynomial.eval_X]`. Use `congr 1`. Simplify using `only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_line (n : ℕ) (Δ : MvPolynomial (Fin n) ℂ) (w : V n) (t : ℂ) :
    (MvPolynomial.aeval (fun i => Polynomial.C (w i) * Polynomial.X) Δ).eval t =
      polyAt n Δ (t • w) := by
  unfold polyAt
  induction Δ using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, MvPolynomial.eval_mul, MvPolynomial.aeval_X,
      MvPolynomial.eval_X]
    congr 1
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    simp
    ring

/- English proof (translation)
Introduce `n Δ w h0`. Establish `hne : MvPolynomial.aeval (fun i => Polynomial.C (w i) * Polynomial.X) Δ ≠ 0`. Introduce `hz`. Apply `h0` to reduce the goal to its premises. Use `eval_line n Δ w 0` as an intermediate fact.

Rewrite `this` using `[hz]`. Simplify using `using this.symm`. Use `(Polynomial.finite_setOfPred_isRoot hne).subset ?_` and prove the remaining obligations. Introduce `t ht`. Simplify using `only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, eval_line]`.

Conclude with `ht`.
-/
theorem lineFinite : lineFiniteStatement := by
  intro n Δ w h0
  have hne : MvPolynomial.aeval (fun i => Polynomial.C (w i) * Polynomial.X) Δ ≠ 0 := by
    intro hz
    apply h0
    have := eval_line n Δ w 0
    rw [hz] at this
    simpa using this.symm
  refine (Polynomial.finite_setOfPred_isRoot hne).subset ?_
  intro t ht
  simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, eval_line]
  exact ht

end ReciprocityTheory.L2DbarEstimates.Norm
