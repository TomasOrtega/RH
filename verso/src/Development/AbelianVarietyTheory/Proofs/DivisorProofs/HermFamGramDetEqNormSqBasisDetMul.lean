import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory.GramChange

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules.

Take a linear combination of the given relations to obtain the conclusion. Treat this case separately. Rewrite the conclusion using the stated equalities.
-/
theorem form_sum_right (nm : HermFam F V) (σ : F →+* ℂ) {ι : Type} (s : Finset ι) (f : ι → V) (x : V) :
    nm.form σ x (∑ i ∈ s, f i) = ∑ i ∈ s, nm.form σ x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h := nm.add_right σ x 0 0
    simp only [add_zero] at h
    linear_combination -h
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, nm.add_right, ih]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem form_sum_left (nm : HermFam F V) (σ : F →+* ℂ) {ι : Type} (s : Finset ι) (f : ι → V) (y : V) :
    nm.form σ (∑ i ∈ s, f i) y = ∑ i ∈ s, nm.form σ (f i) y := by
  rw [← nm.conj_symm σ y, form_sum_right, map_sum]
  exact Finset.sum_congr rfl fun i _ => nm.conj_symm σ y (f i)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem form_smul_left (nm : HermFam F V) (σ : F →+* ℂ) (a : F) (x y : V) :
    nm.form σ (a • x) y = starRingEnd ℂ (σ a) * nm.form σ x y := by
  rw [← nm.conj_symm σ y, nm.smul_right, map_mul, nm.conj_symm]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_eq {d : ℕ} (nm : HermFam F V) (σ : F →+* ℂ) (b : Module.Basis (Fin d) F V) (v : Fin d → V) :
    nm.gram σ v = Matrix.conjTranspose ((b.toMatrix v).map σ) * nm.gram σ ⇑b * (b.toMatrix v).map σ := by
  have hv : ∀ j, v j = ∑ i, b.toMatrix v i j • b i := fun j => by
    simp [Module.Basis.toMatrix_apply, b.sum_repr]
  ext a c
  simp only [HermFam.gram, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.map_apply]
  rw [hv a, hv c, form_sum_left]
  simp_rw [form_smul_left, form_sum_right, nm.smul_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  simp [Complex.star_def]
  ring

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gram_det (F V : Type) [Field F] [AddCommGroup V] [Module F V] (nm : HermFam F V)
    (σ : F →+* ℂ) (d : ℕ) (b : Module.Basis (Fin d) F V) (v : Fin d → V) :
    (nm.gram σ v).det = ((Complex.normSq (σ (b.det v)) : ℝ) : ℂ) * (nm.gram σ ⇑b).det := by
  have hd : ((b.toMatrix v).map σ).det = σ (b.det v) := by
    rw [Module.Basis.det_apply, RingHom.map_det]
    rfl
  rw [gram_eq nm σ b v, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hd,
    Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

end GlobalTheory.GramChange
