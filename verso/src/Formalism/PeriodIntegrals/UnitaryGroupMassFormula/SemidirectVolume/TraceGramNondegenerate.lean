import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.CjTDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjHA

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
open scoped TensorProduct

/- English proof (translation)
Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
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
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trace_basis_holds : TraceBase := by
  intro F E _ _ _ _ R _ _ σ M J x y
  rw [W.hR_ratV R σ J x y]
  exact trace_one_tmul R _

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hE_add_left {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x x' y : Fin M → E) :
    hE σ J (x + x') y = hE σ J x y + hE σ J x' y := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem hE_add_right {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x y y' : Fin M → E) :
    hE σ J x (y + y') = hE σ J x y + hE σ J x y' := by
  simp only [hE, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
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
Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

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
Simplify using the standard rewrite rules.
-/
theorem hE_single {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (x : Fin M → E) (j : Fin M) (c : E) :
    hE σ J x (Pi.single j c) = (∑ i, σ (x i) * J i j) * c := by
  simp [hE, Formalism.UG.hform, Pi.single_apply, Finset.sum_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
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
