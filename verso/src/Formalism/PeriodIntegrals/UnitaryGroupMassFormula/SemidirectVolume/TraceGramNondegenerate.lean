import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CjTDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjHA

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

/- English proof (translation)
Establish `h : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] z) = (Algebra.lmul F E z).baseChange R`. Apply `TensorProduct.AlgebraTensorModule.ext` to reduce the goal to its premises. Introduce `r e`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Rewrite using `[Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]`.
-/
theorem trace_one_tmul {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (z : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] z) = algebraMap F R (Algebra.trace F E z) := by
  have h : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] z) = (Algebra.lmul F E z).baseChange R := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r e
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

/- English proof (translation)
Introduce `F E _ _ _ _ R _ _ σ M J x y`. Rewrite using `[W.hR_ratV R σ J x y]`. Conclude with `trace_one_tmul R _`.
-/
theorem trace_basis_holds : TraceBase := by
  intro F E _ _ _ _ R _ _ σ M J x y
  rw [W.hR_ratV R σ J x y]
  exact trace_one_tmul R _

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem hE_add_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → E) :
    hE σ J (x + x') y = hE σ J x y + hE σ J x' y := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem hE_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → E) :
    hE σ J x (y + y') = hE σ J x y + hE σ J x y' := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Establish `hc : (σ : E →+* E) (algebraMap F E c) = algebraMap F E c` using `σ.commutes c`. Rewrite using `[map_mul, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_smul_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (c : F) (x y : Fin M → E) :
    hE σ J (c • x) y = algebraMap F E c * hE σ J x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (σ : E →+* E) (algebraMap F E c) = algebraMap F E c := σ.commutes c
  rw [map_mul, hc]
  ring

/- English proof (translation)
Simplify using `only [hE, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hE_smul_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (c : F) (x y : Fin M → E) :
    hE σ J x (c • y) = algebraMap F E c * hE σ J x y := by
  simp only [hE, Formalism.UG.hform, Pi.smul_apply, Algebra.smul_def]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

def trForm {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) : LinearMap.BilinForm F (Fin M → E) :=
  LinearMap.mk₂ F (fun x y => Algebra.trace F E (hE σ J x y))
    (fun x x' y => by simp only [hE_add_left, map_add])
    (fun c x y => by simp only [hE_smul_left, ← Algebra.smul_def, map_smul])
    (fun x y y' => by simp only [hE_add_right, map_add])
    (fun c x y => by simp only [hE_smul_right, ← Algebra.smul_def, map_smul])

/- English proof (translation)
Simplify using `[hE, Formalism.UG.hform, Pi.single_apply, Finset.sum_mul]`.
-/
theorem hE_single {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) (j : Fin M) (c : E) :
    hE σ J x (Pi.single j c) = (∑ i, σ (x i) * J i j) * c := by
  simp [hE, Formalism.UG.hform, Pi.single_apply, Finset.sum_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ k b`. Establish `hfin : FiniteDimensional F E` using `Module.finite_of_finrank_eq_succ hCM.2.2.1`. Establish `hG : (Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))) = LinearMap.BilinForm.toMatrix b (trForm σ J)`. Use extensionality with `i j`. Simplify using `[trForm, LinearMap.BilinForm.toMatrix_apply]`.

Rewrite using `[hG, ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]`. Use `LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft ?_` and prove the remaining obligations. Introduce `x hx`. Establish `hrow : ∀ j, ∑ i, σ (x i) * J i j = 0`. Introduce `j`.

Apply `(traceForm_nondegenerate F E).1` to reduce the goal to its premises. Introduce `c`. Establish `h1` using `hx (Pi.single j c)`. Simplify using `only [trForm, LinearMap.mk₂_apply] at h1`. Rewrite using `[Algebra.traceForm_apply, ← hE_single]`.

Conclude with `h1`. Establish `hv : Matrix.vecMul (fun i => σ (x i)) J = 0` using `funext fun j => by`. Simplify `hrow j` using `[Matrix.vecMul, dotProduct]`. Assume the negation of the conclusion as `hx0`. Establish `hne : (fun i => σ (x i)) ≠ 0`.

Introduce `h`. Apply `hx0` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `congrFun h i` as an intermediate fact. Simplify using `using this`.

Conclude with `hJ.2 (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hv⟩)`.
-/
theorem trace_gram_nondegenerate : TraceGramND := by
  intro F E _ _ _ _ _ σ hCM M J hJ k b
  have hfin : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hCM.2.2.1
  have hG : (Matrix.of fun i j => Algebra.trace F E (hE σ J (b i) (b j))) =
      LinearMap.BilinForm.toMatrix b (trForm σ J) := by
    ext i j
    simp [trForm, LinearMap.BilinForm.toMatrix_apply]
  rw [hG, ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
  refine LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft ?_
  intro x hx
  have hrow : ∀ j, ∑ i, σ (x i) * J i j = 0 := by
    intro j
    apply (traceForm_nondegenerate F E).1
    intro c
    have h1 := hx (Pi.single j c)
    simp only [trForm, LinearMap.mk₂_apply] at h1
    rw [Algebra.traceForm_apply, ← hE_single]
    exact h1
  have hv : Matrix.vecMul (fun i => σ (x i)) J = 0 := funext fun j => by
    simpa [Matrix.vecMul, dotProduct] using hrow j
  by_contra hx0
  have hne : (fun i => σ (x i)) ≠ 0 := by
    intro h
    apply hx0
    funext i
    have := congrFun h i
    simpa using this
  exact hJ.2 (Matrix.exists_vecMul_eq_zero_iff.mp ⟨_, hne, hv⟩)

end PI.VolSemiDirect.W.Cj
