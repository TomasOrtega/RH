import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Height
import GroundTheory.AutomorphicForms.TraceFormulaConvolution
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsAreCuspForms
import GroundTheory.AutomorphicForms.MultiplicityOne.OpenSubgroupRep
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteLevelGroups
import GroundTheory.AutomorphicForms.MultiplicityOne.FiniteAdelicHaar
import GroundTheory.AutomorphicForms.L2LocalComponents.CenterCommute

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul c x`. Use `⟨c.re • x, c.im • x, ?_⟩` and prove the remaining obligations. Rewrite using `[← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]`.

Use `congr 1`. Apply the tactic sequence `apply Complex.ext <;> simp`. Consider the case `add x y hx hy`. Take `⟨a, b, rfl⟩` from `hx`. Take `⟨c, d, rfl⟩` from `hy`.

Use `⟨a + c, b + d, ?_⟩` and prove the remaining obligations. Rewrite using `[TensorProduct.tmul_add, TensorProduct.tmul_add]`. Normalize the expressions using the abelian group laws.
-/
private theorem centerC_ex (A : Type) [Ring A] [Algebra ℝ A] (z : ℂ ⊗[ℝ] A) :
    ∃ a b : A, z = (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul c x =>
    refine ⟨c.re • x, c.im • x, ?_⟩
    rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul]
    congr 1
    apply Complex.ext <;> simp
  | add x y hx hy =>
    obtain ⟨a, b, rfl⟩ := hx
    obtain ⟨c, d, rfl⟩ := hy
    refine ⟨a + c, b + d, ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel

/- English proof (translation)
Establish `h1` using `congrArg (fun w => TensorProduct.lid ℝ A (LinearMap.rTensor A Complex.reLm w)) h`. Establish `h2` using `congrArg (fun w => TensorProduct.lid ℝ A (LinearMap.rTensor A Complex.imLm w)) h`. Simplify using `at h1 h2`. Conclude with `⟨h1, h2⟩`.
-/
private theorem centerC_uniq (A : Type) [Ring A] [Algebra ℝ A] (a b c d : A)
    (h : (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b = (1 : ℂ) ⊗ₜ[ℝ] c + Complex.I ⊗ₜ[ℝ] d) :
    a = c ∧ b = d := by
  have h1 := congrArg (fun w => TensorProduct.lid ℝ A (LinearMap.rTensor A Complex.reLm w)) h
  have h2 := congrArg (fun w => TensorProduct.lid ℝ A (LinearMap.rTensor A Complex.imLm w)) h
  simp at h1 h2
  exact ⟨h1, h2⟩

/- English proof (translation)
Introduce `A _ _ z`. Use `⟨centerC_ex A z, ?_⟩` and prove the remaining obligations. Introduce and unpack `a b rfl`. Simplify using `only [Subalgebra.mem_center_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `key : ∀ x : A, x * a = a * x ∧ x * b = b * x`. Introduce `x`. Establish `hx` using `h ((1 : ℂ) ⊗ₜ[ℝ] x)`. Simplify using `only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at hx`.

Conclude with `centerC_uniq A _ _ _ _ hx`. Conclude with `⟨fun x => (key x).1, fun x => (key x).2⟩`. Introduce and unpack `⟨ha, hb⟩ w`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul c x`. Simplify using `only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ha x, hb x, mul_comm c Complex.I]`. Consider the case `add x y hx hy => rw [add_mul, mul_add (_ + _) x y, hx, hy]`.
-/
theorem UpperTheory.ConvolutionTheory.Tf.centerC :
    ∀ (A : Type) [Ring A] [Algebra ℝ A] (z : ℂ ⊗[ℝ] A), (∃ a b : A, z = (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b) ∧
      ∀ a b : A, z = (1 : ℂ) ⊗ₜ[ℝ] a + Complex.I ⊗ₜ[ℝ] b →
        (z ∈ Subalgebra.center ℂ (ℂ ⊗[ℝ] A) ↔ a ∈ Subalgebra.center ℝ A ∧ b ∈ Subalgebra.center ℝ A) := by
  intro A _ _ z
  refine ⟨centerC_ex A z, ?_⟩
  rintro a b rfl
  simp only [Subalgebra.mem_center_iff]
  constructor
  · intro h
    have key : ∀ x : A, x * a = a * x ∧ x * b = b * x := by
      intro x
      have hx := h ((1 : ℂ) ⊗ₜ[ℝ] x)
      simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at hx
      exact centerC_uniq A _ _ _ _ hx
    exact ⟨fun x => (key x).1, fun x => (key x).2⟩
  · rintro ⟨ha, hb⟩ w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
      simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, ha x, hb x,
        mul_comm c Complex.I]
    | add x y hx hy => rw [add_mul, mul_add (_ + _) x y, hx, hy]
