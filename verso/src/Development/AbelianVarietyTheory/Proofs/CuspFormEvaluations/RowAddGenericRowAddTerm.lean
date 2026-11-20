import Mathlib

open MvPolynomial

namespace GlobalTheory

section RowAdd

variable {K σ ι : Type*} [Field K] [DecidableEq σ] [Fintype ι]

noncomputable def rowAddTerm (K : Type*) [Field K] (u w : ι → σ) (s : σ) : MvPolynomial σ K :=
  ∑ k, if s = w k then X (u k) else 0

noncomputable def rowAddGeneric (u w : ι → σ) :
    MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  aeval fun s => Polynomial.C (X s) + Polynomial.X * Polynomial.C (rowAddTerm K u w s)

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp [rowAddGeneric, Polynomial.algebraMap_apply]`. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p s hp`. Rewrite using `[map_mul, Polynomial.eval_mul, hp, map_mul]`.

Use `congr 1`. Simplify using `[rowAddGeneric, rowAddTerm, Finset.mul_sum, Polynomial.eval_finsetSum]`. Simplify using `only [mul_comm]`.
-/
theorem eval_rowAddGeneric (u w : ι → σ) (t : K) (P : MvPolynomial σ K) :
    Polynomial.eval (C t) (rowAddGeneric u w P) =
      bind₁ (fun s => X s + ∑ k, if s = w k then C t * X (u k) else 0) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowAddGeneric, Polynomial.algebraMap_apply]
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul]
    congr 1
    simp [rowAddGeneric, rowAddTerm, Finset.mul_sum, Polynomial.eval_finsetSum]
    simp only [mul_comm]

/- English proof (translation)
Establish `h` using `eval_rowAddGeneric u w (0 : K) P`. Simplify using `using h`.
-/
theorem eval_zero_rowAddGeneric (u w : ι → σ) (P : MvPolynomial σ K) :
    Polynomial.eval 0 (rowAddGeneric u w P) = P := by
  have h := eval_rowAddGeneric u w (0 : K) P
  simpa using h

/- English proof (translation)
Establish `h0 : ∀ k, rowAddTerm K u w (u k) = 0` using `fun k => by`. Simplify using `[rowAddTerm, huw k]`. Use `conv_lhs => rw [rowAddTerm]`. Use `conv_rhs => rw [rowAddTerm]`. Rewrite using `[map_sum, map_sum]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `split_ifs`. Simplify using `[rowAddGeneric, h0]`. Simplify using the standard rewrite rules.
-/
theorem rowAddGeneric_rowAddTerm (u w : ι → σ) (huw : ∀ k l, u k ≠ w l) (s : σ) :
    rowAddGeneric u w (rowAddTerm K u w s) = Polynomial.C (rowAddTerm K u w s) := by
  have h0 : ∀ k, rowAddTerm K u w (u k) = 0 := fun k => by
    simp [rowAddTerm, huw k]
  conv_lhs => rw [rowAddTerm]
  conv_rhs => rw [rowAddTerm]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs
  · simp [rowAddGeneric, h0]
  · simp

/- English proof (translation)
Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Simplify using `[h]`. Simplify using `[pderiv_X_of_ne h]`.
-/
theorem sum_X_mul_pderiv_X (u w : ι → σ) (s : σ) :
    ∑ k, X (u k) * pderiv (w k) (X s : MvPolynomial σ K) = rowAddTerm K u w s := by
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs with h
  · simp [h]
  · simp [pderiv_X_of_ne h]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a => simp [rowAddGeneric, Polynomial.algebraMap_apply]`. Consider the case `add p q hp hq`. Simplify using `only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]`. Consider the case `mul_X p s hp`.

Establish `h : ∑ k, X (u k) * pderiv (w k) (p * X s) = (∑ k, X (u k) * pderiv (w k) p) * X s + p * rowAddTerm K u w s`. Rewrite using `[← sum_X_mul_pderiv_X, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h, map_add, map_mul (rowAddGeneric u w), map_mul (rowAddGeneric u w), map_mul (rowAddGeneric u w), Polynomial.derivative_mul, hp, rowAddGeneric_rowAddTerm u w huw]`. Establish `hX : Polynomial.derivative (rowAddGeneric u w (X s : MvPolynomial σ K)) = Polynomial.C (rowAddTerm K u w s)`. Simplify using `[rowAddGeneric]`. Rewrite using `[hX]`.
-/
theorem derivative_rowAddGeneric (u w : ι → σ) (huw : ∀ k l, u k ≠ w l)
    (P : MvPolynomial σ K) :
    Polynomial.derivative (rowAddGeneric u w P) =
      rowAddGeneric u w (∑ k, X (u k) * pderiv (w k) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [rowAddGeneric, Polynomial.algebraMap_apply]
  | add p q hp hq =>
    simp only [map_add, mul_add, Finset.sum_add_distrib, hp, hq]
  | mul_X p s hp =>
    have h : ∑ k, X (u k) * pderiv (w k) (p * X s) =
        (∑ k, X (u k) * pderiv (w k) p) * X s + p * rowAddTerm K u w s := by
      rw [← sum_X_mul_pderiv_X, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    rw [h, map_add, map_mul (rowAddGeneric u w), map_mul (rowAddGeneric u w),
      map_mul (rowAddGeneric u w), Polynomial.derivative_mul, hp,
      rowAddGeneric_rowAddTerm u w huw]
    have hX : Polynomial.derivative (rowAddGeneric u w (X s : MvPolynomial σ K)) =
        Polynomial.C (rowAddTerm K u w s) := by
      simp [rowAddGeneric]
    rw [hX]

end RowAdd

set_option linter.unusedVariables false in

/- English proof (translation)
Use `tfae_have 2 → 1 := fun h t => h t`. Use `tfae_have 1 → 3 := by`. Introduce `h`. Establish `hc : rowAddGeneric u w P = Polynomial.C P`. Apply `Polynomial.eq_of_infinite_eval_eq` to reduce the goal to its premises.

Establish `hinj : Function.Injective fun t : ℤ => (C (t : K) : MvPolynomial σ K)` using `fun a b hab => Int.cast_injective (C_injective σ K hab)`. Use `Set.infinite_of_injective_forall_mem hinj fun t => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_ofPred_eq, Polynomial.eval_C]`. Rewrite using `[eval_rowAddGeneric, h t]`. Establish `hd` using `derivative_rowAddGeneric u w huw P`.

Rewrite `hd` using `[hc, Polynomial.derivative_C]`. Rewrite using `[← eval_zero_rowAddGeneric u w (∑ k, X (u k) * pderiv (w k) P), ← hd, Polynomial.eval_zero]`. Use `tfae_have 3 → 2 := by`. Introduce `h t`. Establish `hd` using `derivative_rowAddGeneric u w huw P`.

Rewrite `hd` using `[h, map_zero]`. Establish `hc` using `Polynomial.eq_C_of_derivative_eq_zero hd`. Rewrite using `[← eval_rowAddGeneric]`. Use `conv_rhs => rw [← eval_zero_rowAddGeneric u w P]`. Rewrite using `[hc, Polynomial.eval_C, Polynomial.eval_C]`.

Use `tfae_finish`.
-/
theorem rowAdd_invariant_iff {K σ ι : Type*} [Field K] [CharZero K] [DecidableEq σ] [Fintype ι]
    (u w : ι → σ) (hw : Function.Injective w)
    (huw : ∀ k l, u k ≠ w l) (P : MvPolynomial σ K) :
    List.TFAE [∀ t : ℤ, bind₁ (fun s => X s + ∑ k, if s = w k then C (t : K) * X (u k) else 0) P = P,
      ∀ t : K, bind₁ (fun s => X s + ∑ k, if s = w k then C t * X (u k) else 0) P = P,
      ∑ k, X (u k) * pderiv (w k) P = 0] := by
  tfae_have 2 → 1 := fun h t => h t
  tfae_have 1 → 3 := by
    intro h
    have hc : rowAddGeneric u w P = Polynomial.C P := by
      apply Polynomial.eq_of_infinite_eval_eq
      have hinj : Function.Injective fun t : ℤ => (C (t : K) : MvPolynomial σ K) :=
        fun a b hab => Int.cast_injective (C_injective σ K hab)
      refine Set.infinite_of_injective_forall_mem hinj fun t => ?_
      simp only [Set.mem_ofPred_eq, Polynomial.eval_C]
      rw [eval_rowAddGeneric, h t]
    have hd := derivative_rowAddGeneric u w huw P
    rw [hc, Polynomial.derivative_C] at hd
    rw [← eval_zero_rowAddGeneric u w (∑ k, X (u k) * pderiv (w k) P), ← hd, Polynomial.eval_zero]
  tfae_have 3 → 2 := by
    intro h t
    have hd := derivative_rowAddGeneric u w huw P
    rw [h, map_zero] at hd
    have hc := Polynomial.eq_C_of_derivative_eq_zero hd
    rw [← eval_rowAddGeneric]
    conv_rhs => rw [← eval_zero_rowAddGeneric u w P]
    rw [hc, Polynomial.eval_C, Polynomial.eval_C]
  tfae_finish

end GlobalTheory
