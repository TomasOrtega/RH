import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HookLengthBound.DetShiftNormOf
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ProdFactorialSupportSubSingle
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFockqLemmas

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace PI.HookSteps

/- English proof (translation)
Introduce `σ v f g`. Apply `(Rat.castHom ℂ).injective` to reduce the goal to its premises. Use `show ((fockQ (X v * f) g : ℚ) : ℂ) = ((fockQ f (pderiv v g) : ℚ) : ℂ)`. Rewrite using `[lfockq_cast, lfockq_cast, map_mul, map_X, Formalism.REAL.fischerInner_X_mul_left, pderiv_map]`.
-/
theorem mulXAdj : MulXAdj := by
  intro σ v f g
  classical
  apply (Rat.castHom ℂ).injective
  show ((fockQ (X v * f) g : ℚ) : ℂ) = ((fockQ f (pderiv v g) : ℚ) : ℂ)
  rw [lfockq_cast, lfockq_cast, map_mul, map_X, Formalism.REAL.fischerInner_X_mul_left, pderiv_map]

/- English proof (translation)
Unfold `fockQ`. Use `Finset.sum_subset h fun m _ hm => ?_` and prove the remaining obligations. Establish `: f.coeff m = 0` using `by simpa using hm`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem fockQ_eq_sum_of_support_subset_of_type {σ : Type*} (f g : MvPolynomial σ ℚ) (S : Finset (σ →₀ ℕ))
    (h : f.support ⊆ S) :
    fockQ f g = ∑ m ∈ S, f.coeff m * g.coeff m * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℚ) := by
  unfold fockQ
  refine Finset.sum_subset h fun m _ hm => ?_
  have : f.coeff m = 0 := by simpa using hm
  rw [this]
  ring

/- English proof (translation)
Unfold `fockQ`. Simplify using the standard rewrite rules.
-/
theorem fockQ_zero_left {σ : Type*} (g : MvPolynomial σ ℚ) : fockQ 0 g = 0 := by
  unfold fockQ
  simp

/- English proof (translation)
Conclude with `Finset.induction_on s (by simp [fockQ_zero_left]) fun a s ha ih => by`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, lfockq_add_left, ih]`.
-/
theorem fockQ_sum_left {σ ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ ℚ) (g : MvPolynomial σ ℚ) :
    fockQ (∑ i ∈ s, F i) g = ∑ i ∈ s, fockQ (F i) g := by
  classical
  exact Finset.induction_on s (by simp [fockQ_zero_left]) fun a s ha ih => by
    rw [Finset.sum_insert ha, Finset.sum_insert ha, lfockq_add_left, ih]

/- English proof (translation)
Unfold `fockQ`. Simplify using `only [MvPolynomial.coeff_sum, Finset.mul_sum, Finset.sum_mul]`. Conclude with `Finset.sum_comm`.
-/
theorem fockQ_sum_right {σ ι : Type*} (s : Finset ι) (F : ι → MvPolynomial σ ℚ) (f : MvPolynomial σ ℚ) :
    fockQ f (∑ i ∈ s, F i) = ∑ i ∈ s, fockQ f (F i) := by
  unfold fockQ
  simp only [MvPolynomial.coeff_sum, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

/- English proof (translation)
Rewrite using `[← Int.cast_smul_eq_zsmul ℚ z f, fockQ_eq_sum_of_support_subset_of_type _ g f.support MvPolynomial.support_smul]`. Unfold `fockQ`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockQ_zsmul_left {σ : Type*} (z : ℤ) (f g : MvPolynomial σ ℚ) :
    fockQ (z • f) g = (z : ℚ) * fockQ f g := by
  rw [← Int.cast_smul_eq_zsmul ℚ z f, fockQ_eq_sum_of_support_subset_of_type _ g f.support MvPolynomial.support_smul]
  unfold fockQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Rewrite using `[← Int.cast_smul_eq_zsmul ℚ z g]`. Unfold `fockQ`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.coeff_smul, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fockQ_zsmul_right {σ : Type*} (z : ℤ) (f g : MvPolynomial σ ℚ) :
    fockQ f (z • g) = (z : ℚ) * fockQ f g := by
  rw [← Int.cast_smul_eq_zsmul ℚ z g]
  unfold fockQ
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Proceed by induction on `l generalizing f g with`. Consider the case `nil => simp`. Consider the case `cons v l ih`. Simplify using `only [List.map_cons, List.prod_cons]`. Rewrite using `[mul_assoc, mul_left_comm, ih, hX σ v]`.

Both sides reduce to the same expression.
-/
theorem fockQ_listX (hX : MulXAdj) {σ : Type} (l : List σ) (f g : MvPolynomial σ ℚ) :
    fockQ ((l.map fun v => (X v : MvPolynomial σ ℚ)).prod * f) g =
      fockQ f ((l.map fun v => ((pderiv v : Derivation ℚ _ _).toLinearMap :
        Module.End ℚ (MvPolynomial σ ℚ))).prod g) := by
  induction l generalizing f g with
  | nil => simp
  | cons v l ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [mul_assoc, mul_left_comm, ih, hX σ v]
    rfl

/- English proof (translation)
Introduce `N f g`. Rewrite using `[detX, Matrix.det_apply, Finset.sum_mul, fockQ_sum_left, detD, LinearMap.sum_apply, fockQ_sum_right]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Units.smul_def, smul_mul_assoc, fockQ_zsmul_left, LinearMap.smul_apply, fockQ_zsmul_right]`. Use `congr 1`.

Establish `h` using `fockQ_listX hX (List.ofFn fun j : Fin N => (σ j, j)) f g`. Simplify using `only [List.map_ofFn] at h`. Rewrite `h` using `[List.prod_ofFn]`. Conclude with `h`.
-/
theorem detAdj_of (hX : MulXAdj) : DetAdj := by
  intro N f g
  classical
  rw [detX, Matrix.det_apply, Finset.sum_mul, fockQ_sum_left, detD, LinearMap.sum_apply,
    fockQ_sum_right]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, smul_mul_assoc, fockQ_zsmul_left, LinearMap.smul_apply, fockQ_zsmul_right]
  congr 1
  have h := fockQ_listX hX (List.ofFn fun j : Fin N => (σ j, j)) f g
  simp only [List.map_ofFn] at h
  rw [List.prod_ofFn] at h
  exact h

/- English proof (translation)
The claim follows from `detAdj_of mulXAdj`.
-/
theorem determinant_adjugate : DetAdj := detAdj_of mulXAdj

end PI.HookSteps
