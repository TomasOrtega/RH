import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.FrameDil

noncomputable section

open scoped Matrix

namespace PositivityTheory.SiegelWeilFormula.Act.CL

section Alg

variable {R : Type} [CommRing R] {n : ℕ} (i₀ : Fin n)

def dg (x y : R) (u : Fin n ⊕ Fin n) : R := if u = Sum.inl i₀ then x else if u = Sum.inr i₀ then y else 1

/- English proof (translation)
Use extensionality with `u v`. Rewrite using `[dM_apply, Matrix.diagonal_apply, dg]`.
-/
theorem dM_eq_diag (x y : R) : dM i₀ x y = Matrix.diagonal (dg i₀ x y) := by
  ext u v
  rw [dM_apply, Matrix.diagonal_apply, dg]

def wM (a b : R) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  1 - Matrix.single (Sum.inl i₀) (Sum.inl i₀) 1 - Matrix.single (Sum.inr i₀) (Sum.inr i₀) 1 +
    Matrix.single (Sum.inl i₀) (Sum.inr i₀) a + Matrix.single (Sum.inr i₀) (Sum.inl i₀) b

/- English proof (translation)
Simplify using `only [wM, Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply]`. Apply the tactic sequence `rcases u with u | u <;> rcases v with v | v <;> simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false, false_and, if_false, sub_zero, add_zero, zero_add, and_self] <;> by_cases h : u = v <;> by_cases h' : u = i₀ <;> subst_vars <;> simp_all [eq_comm]`.
-/
theorem wM_apply (a b : R) (u v : Fin n ⊕ Fin n) :
    wM i₀ a b u v = if u = Sum.inl i₀ then (if v = Sum.inr i₀ then a else 0) else if u = Sum.inr i₀ then
      (if v = Sum.inl i₀ then b else 0) else if u = v then 1 else 0 := by
  simp only [wM, Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply, Matrix.one_apply]
  rcases u with u | u <;> rcases v with v | v <;> simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
    false_and, if_false, sub_zero, add_zero, zero_add, and_self] <;> by_cases h : u = v <;> by_cases h' : u = i₀ <;>
    subst_vars <;> simp_all [eq_comm]

/- English proof (translation)
Rewrite using `[dM_eq_diag, dM_eq_diag]`. Use extensionality with `u v`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, wM_apply, dg, dg]`. Apply the tactic sequence `rcases u with u | u <;> rcases v with v | v <;> simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false] <;>`. Apply the tactic sequence `by_cases h : u = v <;> by_cases h' : u = i₀ <;> by_cases h'' : v = i₀ <;> subst_vars <;> simp_all [mul_comm]`.
-/
theorem wM_dM (a b x y : R) : wM i₀ a b * dM i₀ x y = dM i₀ y x * wM i₀ a b := by
  rw [dM_eq_diag, dM_eq_diag]
  ext u v
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, wM_apply, dg, dg]
  rcases u with u | u <;> rcases v with v | v <;> simp only [Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, if_false] <;>
    by_cases h : u = v <;> by_cases h' : u = i₀ <;> by_cases h'' : v = i₀ <;> subst_vars <;> simp_all [mul_comm]

/- English proof (translation)
The claim follows from `Matrix.single_mul_single_of_ne c i j k h d`.
-/
theorem smz {i j k l : Fin n ⊕ Fin n} (h : j ≠ k) (c d : R) : Matrix.single i j c * Matrix.single k l d = 0 :=
  Matrix.single_mul_single_of_ne c i j k h d

/- English proof (translation)
Establish `n1 : (Sum.inl i₀ : Fin n ⊕ Fin n) ≠ Sum.inr i₀` using `by simp`. Establish `n2 : (Sum.inr i₀ : Fin n ⊕ Fin n) ≠ Sum.inl i₀` using `by simp`. Simplify using `only [wM, sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, Matrix.single_mul_single_same, smz n1, smz n2, h1, h2]`. Normalize the expressions using the abelian group laws.
-/
theorem wM_mul (a b a' b' : R) (h1 : a * b' = 1) (h2 : b * a' = 1) : wM i₀ a b * wM i₀ a' b' = 1 := by
  have n1 : (Sum.inl i₀ : Fin n ⊕ Fin n) ≠ Sum.inr i₀ := by simp
  have n2 : (Sum.inr i₀ : Fin n ⊕ Fin n) ≠ Sum.inl i₀ := by simp
  simp only [wM, sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, Matrix.single_mul_single_same,
    smz n1, smz n2, h1, h2]
  abel

/- English proof (translation)
Rewrite using `[dM_eq_diag]`. Use extensionality with `u v`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`. Distinguish the cases in `huv : u = v`. Substitute `huv` using the available equality.

Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hu : u ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin n ⊕ Fin n))`. Rewrite using `[(hJ u hu v).1, Matrix.one_apply_ne huv]`. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hv : v ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin n ⊕ Fin n))`.

Rewrite using `[(hJ v hv u).2, Matrix.one_apply_ne huv]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu hv`. Rewrite using `[dg, dg, if_neg hu.1, if_neg hu.2, if_neg hv.1, if_neg hv.2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem comm_dM (J : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (hJ : ∀ u ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin n ⊕ Fin n)), ∀ v,
      J u v = (1 : Matrix _ _ R) u v ∧ J v u = (1 : Matrix _ _ R) v u) (x y : R) :
    J * dM i₀ x y = dM i₀ x y * J := by
  rw [dM_eq_diag]
  ext u v
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases huv : u = v
  · subst huv; ring
  · by_cases hu : u ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin n ⊕ Fin n))
    · rw [(hJ u hu v).1, Matrix.one_apply_ne huv]; ring
    · by_cases hv : v ∈ ({Sum.inl i₀, Sum.inr i₀} : Set (Fin n ⊕ Fin n))
      · rw [(hJ v hv u).2, Matrix.one_apply_ne huv]; ring
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hu hv
        rw [dg, dg, if_neg hu.1, if_neg hu.2, if_neg hv.1, if_neg hv.2]; ring

end Alg

end PositivityTheory.SiegelWeilFormula.Act.CL

end
