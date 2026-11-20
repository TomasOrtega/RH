import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PBoundT

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Take a linear combination of the given relations to obtain the conclusion.

A detailed English derivation is pending.
-/
lemma entry {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ)
    (h : (diagonal l)ᴴ * J * diagonal l = J) (i j : Fin n) (hJ : J i j ≠ 0) :
    star (l i) * l j = 1 := by
  have e := congrFun (congrFun h i) j
  rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul] at e
  have e2 : (star (l i) * l j - 1) * J i j = 0 := by
    simp only [Pi.star_apply] at e
    linear_combination e
  exact sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hJ)

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
lemma norm_entry {n : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ)
    (h : (diagonal l)ᴴ * J * diagonal l = J) (i j : Fin n) (hJ : J i j ≠ 0) :
    ‖l i‖ * ‖l j‖ = 1 := by
  have e := congrArg (fun x : ℂ => ‖x‖) (entry J l h i j hJ)
  simpa [norm_mul, norm_star] using e

end MainStatements.WeightKernel.PBoundT

namespace MainStatements.WeightKernel

open PBoundT in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem boundT : BoundT := by
  intro n J l hdet hinj hl a b ha
  refine ⟨max b (max (1 / a) 1), ?_⟩
  intro τ hτ hbd j
  have col : ∃ i, J i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : J.det = 0 := Matrix.det_eq_zero_of_column_eq_zero j hc
    rw [this] at hdet
    exact not_isUnit_zero hdet
  obtain ⟨i, hij⟩ := col
  have hl2 := norm_entry J l hl i j hij
  have hτ2 := norm_entry J τ hτ i j hij
  rcases lt_trichotomy ‖l j‖ 1 with hlt | heq | hgt
  · have hli : 1 < ‖l i‖ := by
      by_contra hc
      push_neg at hc
      have h0 : 0 ≤ ‖l j‖ := norm_nonneg _
      nlinarith
    have ha' := (hbd i hli).1
    have hτj : ‖τ j‖ ≤ 1 / a := by
      rw [le_div_iff₀ ha]
      have h0 : 0 ≤ ‖τ j‖ := norm_nonneg _
      nlinarith
    exact le_trans hτj (le_trans (le_max_left _ _) (le_max_right _ _))
  · have hli : ‖l i‖ = 1 := by
      rw [heq, mul_one] at hl2
      exact hl2
    have ent := entry J l hl i j hij
    have hsq : l i * star (l i) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hli]
      simp
    have hij' : l i = l j := by
      have : l i * (star (l i) * l j) = l i := by rw [ent, mul_one]
      rw [← mul_assoc, hsq, one_mul] at this
      exact this.symm
    have hieq : i = j := hinj hij'
    subst hieq
    have h0 : 0 ≤ ‖τ i‖ := norm_nonneg _
    have h1 : ‖τ i‖ = 1 := by nlinarith
    rw [h1]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  · exact le_trans (hbd j hgt).2 (le_max_left _ _)

end MainStatements.WeightKernel

end
