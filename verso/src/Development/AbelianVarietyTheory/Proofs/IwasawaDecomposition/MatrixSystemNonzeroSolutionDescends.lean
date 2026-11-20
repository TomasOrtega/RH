import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SplitRep
open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `hC hAB hQ`. Use `letI := f.toAlgebra`. Choose the witnesses or unpack the hypotheses as in `⟨i₀, j₀, hij⟩ : ∃ i j, C i j ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hC (Matrix.ext h)`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual k L, φ (C i₀ j₀) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hij ((Module.forall_dual_apply_eq_zero_iff k (C i₀ j₀)).mp h)`.

Establish `key : ∀ (x : k) (y : L), φ (f x * y) = x * φ y`. Introduce `x y`. Establish `h1 : f x * y = x • y` using `(Algebra.smul_def x y).symm`. Rewrite using `[h1, map_smul, smul_eq_mul]`. Establish `key' : ∀ (x : k) (y : L), φ (y * f x) = φ y * x`.

Introduce `x y`. Rewrite using `[mul_comm y, key, mul_comm]`. Use `⟨C.map φ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Apply `hφ` to reduce the goal to its premises.

Use `congrFun (congrFun h i₀) j₀` as an intermediate fact. Simplify using `using this`. Introduce `g`. Use extensionality with `i j`. Use `congrArg φ (congrFun (congrFun (hAB g) i) j)` as an intermediate fact.

Simplify `this` using `only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, key']`. Use extensionality with `i j`. Use `congrArg φ (congrFun (congrFun hQ i) j)` as an intermediate fact. Simplify `this` using `only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, Matrix.zero_apply, map_zero]`.
-/
theorem matrix_system_nonzero_solution_descends {k L Γ : Type} [Field k] [Field L] (f : k →+* L)
    {a b c : ℕ} (A : Γ → Matrix (Fin a) (Fin a) k) (B : Γ → Matrix (Fin b) (Fin b) k)
    (Q : Matrix (Fin c) (Fin a) k) (C : Matrix (Fin a) (Fin b) L) :
    C ≠ 0 → (∀ g, (A g).map f * C = C * (B g).map f) → Q.map f * C = 0 →
      ∃ X : Matrix (Fin a) (Fin b) k, X ≠ 0 ∧ (∀ g, A g * X = X * B g) ∧ Q * X = 0 := by
  intro hC hAB hQ
  letI := f.toAlgebra
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hC (Matrix.ext h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k L, φ (C i₀ j₀) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hij ((Module.forall_dual_apply_eq_zero_iff k (C i₀ j₀)).mp h)
  have key : ∀ (x : k) (y : L), φ (f x * y) = x * φ y := by
    intro x y
    have h1 : f x * y = x • y := (Algebra.smul_def x y).symm
    rw [h1, map_smul, smul_eq_mul]
  have key' : ∀ (x : k) (y : L), φ (y * f x) = φ y * x := by
    intro x y
    rw [mul_comm y, key, mul_comm]
  refine ⟨C.map φ, ?_, ?_, ?_⟩
  · intro h
    apply hφ
    have := congrFun (congrFun h i₀) j₀
    simpa using this
  · intro g
    ext i j
    have := congrArg φ (congrFun (congrFun (hAB g) i) j)
    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, key'] using this
  · ext i j
    have := congrArg φ (congrFun (congrFun hQ i) j)
    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, Matrix.zero_apply, map_zero]
      using this

end GlobalTheory
