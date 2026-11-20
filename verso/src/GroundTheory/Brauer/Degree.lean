import Mathlib
import GroundTheory.Brauer.BaseChangeCSA
import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Brauer

open Module TensorProduct

universe u v w

section Degree

variable (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A]

noncomputable def degree : ℕ := Nat.sqrt (finrank K A)

/- English proof (translation)
Take `⟨n, hn, ⟨e⟩⟩` from `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)`. Use `⟨n, hn, ?_, ⟨e⟩⟩` and prove the remaining obligations. Rewrite using `[← finrank_baseChange_eq K (AlgebraicClosure K) A, e.toLinearEquiv.finrank_eq, Module.finrank_matrix, Module.finrank_self]`. Simplify using `[sq]`.
-/
theorem exists_algEquiv_matrix_algebraicClosure [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] :
    ∃ n : ℕ, NeZero n ∧ finrank K A = n ^ 2 ∧
      Nonempty (AlgebraicClosure K ⊗[K] A ≃ₐ[AlgebraicClosure K]
        Matrix (Fin n) (Fin n) (AlgebraicClosure K)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed
    (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
  refine ⟨n, hn, ?_, ⟨e⟩⟩
  rw [← finrank_baseChange_eq K (AlgebraicClosure K) A, e.toLinearEquiv.finrank_eq,
    Module.finrank_matrix, Module.finrank_self]
  simp [sq]

/- English proof (translation)
The claim follows from `let ⟨n, _, h, _⟩ := exists_algEquiv_matrix_algebraicClosure K A ⟨n, h⟩`.
-/
theorem exists_finrank_eq_sq [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] :
    ∃ n : ℕ, finrank K A = n ^ 2 :=
  let ⟨n, _, h, _⟩ := exists_algEquiv_matrix_algebraicClosure K A
  ⟨n, h⟩

/- English proof (translation)
Take `⟨n, h⟩` from `exists_finrank_eq_sq K A`. Rewrite using `[degree, h, Nat.sqrt_eq']`.
-/
theorem finrank_eq_degree_sq [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] :
    finrank K A = degree K A ^ 2 := by
  obtain ⟨n, h⟩ := exists_finrank_eq_sq K A
  rw [degree, h, Nat.sqrt_eq']

/- English proof (translation)
Rewrite using `[finrank_eq_degree_sq K A]`. Conclude with `⟨fun h ↦ h ▸ rfl, fun h ↦ Nat.pow_left_injective two_ne_zero h⟩`.
-/
theorem degree_eq_iff [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A] (n : ℕ) :
    degree K A = n ↔ finrank K A = n ^ 2 := by
  rw [finrank_eq_degree_sq K A]
  exact ⟨fun h ↦ h ▸ rfl, fun h ↦ Nat.pow_left_injective two_ne_zero h⟩

/- English proof (translation)
Rewrite using `[degree, degree, finrank_baseChange_eq]`.
-/
theorem degree_baseChange (L : Type w) [Field L] [Algebra K L] :
    degree L (L ⊗[K] A) = degree K A := by
  rw [degree, degree, finrank_baseChange_eq]

/- English proof (translation)
Rewrite using `[degree, Module.finrank_matrix, finrank_eq_degree_sq K A, ← sq, ← mul_pow, Nat.sqrt_eq']`.
-/
theorem degree_matrix [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
    (ι : Type*) [Fintype ι] [DecidableEq ι] :
    degree K (Matrix ι ι A) = Fintype.card ι * degree K A := by
  rw [degree, Module.finrank_matrix, finrank_eq_degree_sq K A, ← sq, ← mul_pow, Nat.sqrt_eq']

/- English proof (translation)
Rewrite using `[degree, Module.finrank_tensorProduct, finrank_eq_degree_sq K A, finrank_eq_degree_sq K B, ← mul_pow, Nat.sqrt_eq']`.
-/
theorem degree_tensorProduct [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
    (B : Type w) [Ring B] [Algebra K B] [Algebra.IsCentral K B] [IsSimpleRing B]
    [FiniteDimensional K B] :
    degree K (A ⊗[K] B) = degree K A * degree K B := by
  rw [degree, Module.finrank_tensorProduct, finrank_eq_degree_sq K A, finrank_eq_degree_sq K B,
    ← mul_pow, Nat.sqrt_eq']

end Degree

section CSA

variable {K : Type u} [Field K]

@[simp]
/- English proof (translation)
The claim follows from `degree_baseChange K A L @[simp]`.
-/
theorem degree_baseChangeCSA (L : Type w) [Field L] [Algebra K L] (A : CSA.{u, v} K) :
    degree L (baseChangeCSA L A) = degree K A :=
  degree_baseChange K A L

@[simp]
/- English proof (translation)
Establish `h` using `degree_matrix K A (Fin n)`. Rewrite `h` using `[Fintype.card_fin]`. Conclude with `h`. Use the proof step `@[simp]`.
-/
theorem degree_matrixCSA (A : CSA.{u, v} K) (n : ℕ) [NeZero n] :
    degree K (matrixCSA A n) = n * degree K A := by
  have h := degree_matrix K A (Fin n)
  rw [Fintype.card_fin] at h
  exact h

@[simp]
/- English proof (translation)
The claim follows from `degree_tensorProduct K A B`.
-/
theorem degree_tensorCSA (A B : CSA.{u, v} K) :
    degree K (tensorCSA A B) = degree K A * degree K B :=
  degree_tensorProduct K A B

end CSA

section Index

variable (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A]

noncomputable def index : ℕ :=
  sInf {d : ℕ | ∃ (n : ℕ) (_ : NeZero n) (D : Type v) (_ : DivisionRing D) (_ : Algebra K D),
    Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) D) ∧ degree K D = d}

variable {K A}

variable (K A)

variable {K A}

variable (K A)

end Index

end GroundTheory.Brauer
