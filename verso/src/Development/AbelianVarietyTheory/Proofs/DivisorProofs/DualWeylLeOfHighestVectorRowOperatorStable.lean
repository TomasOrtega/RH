import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CoefficientSpaceEqSpanOrbitExtremalVector
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Mem.Gelf GlobalTheory.Mem.GelfCheck GlobalTheory.BrCompare

namespace GlobalTheory.BrCompare

/- English proof (translation)
Unfold `rowDiv`. Proceed by induction on `f using MvPolynomial.induction_on generalizing k with`. Consider the case `C c`. Establish `h : rowGen R a b (C c : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (C c)`. Simplify using `[rowGen]`.

Rewrite using `[h]`. Consider the cases of `k with`. Consider the case `zero => simp [rowE_C, Polynomial.coeff_C]`. Consider the case `succ k => simp`. Consider the case `add p q hp hq`.

Simplify using `only [map_add, Polynomial.coeff_add, ← hp, ← hq]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `mul_X p v hp`. Take `⟨c, s⟩` from `v`. Use `set y : MvPolynomial (Fin r × Fin m) R := if b = c then X (a, s) else 0 with hy`.

Establish `hX : rowGen R a b (X (c, s) : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (X (c, s)) + Polynomial.C y * Polynomial.X`. Rewrite using `[rowGen, aeval_X, hy]`. Distinguish the cases in `h : b = c`. Rewrite using `[if_pos h, if_pos h.symm, mul_comm]`. Rewrite using `[if_neg h, if_neg (Ne.symm h), map_zero, zero_mul]`.

Establish `hx : rowE R r m a b (X (c, s)) = y` using `rowE_X R r m a b c s`. Establish `hy' : rowE R r m a b y = (if a = b then 1 else 0) * y`. Rewrite using `[hy]`. Use `split_ifs with h1 h2 h2`. Rewrite using `[rowE_X, if_pos h2.symm, one_mul]`.

Rewrite using `[rowE_X, if_neg (Ne.symm h2), zero_mul]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish `hs : ∀ j, (rowGen R a b (p * X (c, s))).coeff (j + 1) = (rowGen R a b p).coeff (j + 1) * X (c, s) + (rowGen R a b p).coeff j * y`. Introduce `j`.

Rewrite using `[map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C]`. Establish `h0 : (rowGen R a b (p * X (c, s))).coeff 0 = (rowGen R a b p).coeff 0 * X (c, s)`. Rewrite using `[map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X_zero, Polynomial.coeff_mul_C, add_zero]`. Consider the cases of `k with`. Consider the case `zero`.

Rewrite using `[hs, h0, rowE_mul, hx, ← hp]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Consider the case `succ k`. Rewrite using `[hs, hs, map_add, rowE_mul, rowE_mul, hx, hy', ← hp, ← hp]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rowDiv_succ_rec (R : Type) [CommRing R] {r m : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin m) R) (k : ℕ) :
    ((k : MvPolynomial (Fin r × Fin m) R) + 1) * rowDiv R a b (k + 1) f +
      (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) R) * rowDiv R a b k f =
      rowE R r m a b (rowDiv R a b k f) := by
  unfold rowDiv
  induction f using MvPolynomial.induction_on generalizing k with
  | C c =>
    have h : rowGen R a b (C c : MvPolynomial (Fin r × Fin m) R) = Polynomial.C (C c) := by
      simp [rowGen]
    rw [h]
    cases k with
    | zero => simp [rowE_C, Polynomial.coeff_C]
    | succ k => simp
  | add p q hp hq =>
    simp only [map_add, Polynomial.coeff_add, ← hp, ← hq]
    ring
  | mul_X p v hp =>
    obtain ⟨c, s⟩ := v
    set y : MvPolynomial (Fin r × Fin m) R := if b = c then X (a, s) else 0 with hy
    have hX : rowGen R a b (X (c, s) : MvPolynomial (Fin r × Fin m) R) =
        Polynomial.C (X (c, s)) + Polynomial.C y * Polynomial.X := by
      rw [rowGen, aeval_X, hy]
      by_cases h : b = c
      · rw [if_pos h, if_pos h.symm, mul_comm]
      · rw [if_neg h, if_neg (Ne.symm h), map_zero, zero_mul]
    have hx : rowE R r m a b (X (c, s)) = y := rowE_X R r m a b c s
    have hy' : rowE R r m a b y = (if a = b then 1 else 0) * y := by
      rw [hy]
      split_ifs with h1 h2 h2
      · rw [rowE_X, if_pos h2.symm, one_mul]
      · rw [rowE_X, if_neg (Ne.symm h2), zero_mul]
      · simp
      · simp
    have hs : ∀ j, (rowGen R a b (p * X (c, s))).coeff (j + 1) =
        (rowGen R a b p).coeff (j + 1) * X (c, s) + (rowGen R a b p).coeff j * y := by
      intro j
      rw [map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C,
        Polynomial.coeff_mul_C]
    have h0 : (rowGen R a b (p * X (c, s))).coeff 0 = (rowGen R a b p).coeff 0 * X (c, s) := by
      rw [map_mul, hX, mul_add, ← mul_assoc, Polynomial.coeff_add, Polynomial.coeff_mul_X_zero, Polynomial.coeff_mul_C,
        add_zero]
    cases k with
    | zero =>
      rw [hs, h0, rowE_mul, hx, ← hp]
      push_cast
      ring
    | succ k =>
      rw [hs, hs, map_add, rowE_mul, rowE_mul, hx, hy', ← hp, ← hp]
      push_cast
      ring

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => rw [(rowE_eq_rowDiv K r m a b f).2]`. Conclude with `hf`. Consider the case `succ k ih`. Establish `hrec` using `rowDiv_succ_rec K a b f k`.

Establish `h1 : (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) K) * rowDiv K a b k f ∈ M` using `by split_ifs`. Rewrite using `[one_mul, ← nsmul_eq_mul]`. Conclude with `nsmul_mem ih k`. Simplify using the standard rewrite rules. Establish `h2 : ((k + 1 : ℕ) : K) • rowDiv K a b (k + 1) f ∈ M`.

Rewrite using `[Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_succ, eq_sub_of_add_eq hrec]`. Conclude with `M.sub_mem (h _ ih) h1`. Conclude with `(M.smul_mem_iff (Nat.cast_ne_zero.2 k.succ_ne_zero)).1 h2`.
-/
theorem rowDiv_mem_of_rowE {K : Type} [Field K] [CharZero K] {r m : ℕ} (a b : Fin r)
    (M : Submodule K (MvPolynomial (Fin r × Fin m) K)) (h : ∀ f ∈ M, rowE K r m a b f ∈ M) (k : ℕ)
    {f : MvPolynomial (Fin r × Fin m) K} (hf : f ∈ M) : rowDiv K a b k f ∈ M := by
  induction k with
  | zero => rw [(rowE_eq_rowDiv K r m a b f).2]; exact hf
  | succ k ih =>
    have hrec := rowDiv_succ_rec K a b f k
    have h1 : (if a = b then 1 else 0) * (k : MvPolynomial (Fin r × Fin m) K) * rowDiv K a b k f ∈ M := by
      split_ifs
      · rw [one_mul, ← nsmul_eq_mul]; exact nsmul_mem ih k
      · simp
    have h2 : ((k + 1 : ℕ) : K) • rowDiv K a b (k + 1) f ∈ M := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_succ, eq_sub_of_add_eq hrec]
      exact M.sub_mem (h _ ih) h1
    exact (M.smul_mem_iff (Nat.cast_ne_zero.2 k.succ_ne_zero)).1 h2

/- English proof (translation)
Introduce `K _ _ n ν hν M h0 hE`. Rewrite using `[Formalism.L2.Col.dualWeyl_eq_weyl K le_rfl ν hν, weyl, Submodule.span_le]`. Introduce and unpack `_ ⟨w, rfl⟩`. Proceed by induction on `w with`. Consider the case `nil => exact h0`.

Consider the case `cons x w ih => exact rowDiv_mem_of_rowE x.1 x.2.1 M (hE _ _) x.2.2 ih`.
-/
theorem dualWeyl_le_of_rowE_stable : ∀ (K : Type) [Field K] [CharZero K] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    ∀ M : Submodule K (MvPolynomial (Fin n × Fin n) K), hw K le_rfl ν ∈ M →
      (∀ a b : Fin n, ∀ f ∈ M, rowE K n n a b f ∈ M) → dualWeyl K n n ν ≤ M := by
  intro K _ _ n ν hν M h0 hE
  rw [Formalism.L2.Col.dualWeyl_eq_weyl K le_rfl ν hν, weyl, Submodule.span_le]
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact h0
  | cons x w ih => exact rowDiv_mem_of_rowE x.1 x.2.1 M (hE _ _) x.2.2 ih

end GlobalTheory.BrCompare
