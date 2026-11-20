import ReciprocityTheory.L2DbarEstimates.SymmetricSections.HoloSectionStatement

namespace ReciprocityTheory.L2DbarEstimates.Norm

open Filter Topology Asymptotics

universe u

/- English proof (translation)
Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
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
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
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
