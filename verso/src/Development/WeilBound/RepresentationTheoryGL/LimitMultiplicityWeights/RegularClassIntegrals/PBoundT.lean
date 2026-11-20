import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PBoundT

/- English proof (translation)
Establish `e` using `congrFun (congrFun h i) j`. Rewrite `e` using `[diagonal_conjTranspose, mul_diagonal, diagonal_mul]`. Establish `e2 : (star (l i) * l j - 1) * J i j = 0`. Simplify using `only [Pi.star_apply] at e`. Take the linear combination `e`.

Conclude with `sub_eq_zero.mp ((mul_eq_zero.mp e2).resolve_right hJ)`.
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
Apply the tactic sequence `have e := congrArg (fun x : ℂ => ‖x‖) (entry J l h i j hJ)`. Simplify `e` using `[norm_mul, norm_star]`.
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
Introduce `n J l hdet hinj hl a b ha`. Use `⟨max b (max (1 / a) 1), ?_⟩` and prove the remaining obligations. Introduce `τ hτ hbd j`. Establish `col : ∃ i, J i j ≠ 0`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Establish `: J.det = 0` using `Matrix.det_eq_zero_of_column_eq_zero j hc`. Rewrite `hdet` using `[this]`. Conclude with `not_isUnit_zero hdet`. Take `⟨i, hij⟩` from `col`.

Apply the tactic sequence `have hl2 := norm_entry J l hl i j hij`. Apply the tactic sequence `have hτ2 := norm_entry J τ hτ i j hij`. Break down `lt_trichotomy ‖l j‖ 1 with hlt | heq | hgt` into its components or cases. Establish `hli : 1 < ‖l i‖`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Establish `h0 : 0 ≤ ‖l j‖` using `norm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Establish `ha'` using `(hbd i hli).1`. Establish `hτj : ‖τ j‖ ≤ 1 / a`.

Rewrite using `[le_div_iff₀ ha]`. Establish `h0 : 0 ≤ ‖τ j‖` using `norm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `le_trans hτj (le_trans (le_max_left _ _) (le_max_right _ _))`. Establish `hli : ‖l i‖ = 1`.

Rewrite `hl2` using `[heq, mul_one]`. Conclude with `hl2`. Apply the tactic sequence `have ent := entry J l hl i j hij`. Establish `hsq : l i * star (l i) = 1`. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hli]`.

Simplify using the standard rewrite rules. Establish `hij' : l i = l j`. Establish `: l i * (star (l i) * l j) = l i` using `by rw [ent, mul_one]`. Rewrite `this` using `[← mul_assoc, hsq, one_mul]`. Conclude with `this.symm`.

Establish `hieq : i = j` using `hinj hij'`. Substitute `hieq` using the available equality. Establish `h0 : 0 ≤ ‖τ i‖` using `norm_nonneg _`. Establish `h1 : ‖τ i‖ = 1` using `by nlinarith`. Rewrite using `[h1]`.

Conclude with `le_trans (le_max_right _ _) (le_max_right _ _)`. Conclude with `le_trans (hbd j hgt).2 (le_max_left _ _)`.
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
