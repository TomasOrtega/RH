import Mathlib
import Formalism.DegreeFormula.PointDegree.PowSum
import Formalism.DegreeFormula.PointDegree.PermExpInj
import Development.AbelianVarietyTheory.Definitions.Foundations.CurveCl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeVandermonde

open MvPolynomial Finset Formalism.DegreeFormula

namespace GlobalTheory.FlagPoly

open MvPolynomial Finset in
/- English proof (translation)
Rewrite using `[Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]`. Repeatedly rewrite using `[mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, ← map_natCast (C : ℝ →+* MvPolynomial σ ℝ), ← mul_assoc, ← map_mul, coeff_C_mul, coeff_prod_X_pow]`. Establish `hsum : ∑ i, d i = n`. Rewrite using `[← hd, Finsupp.degree_eq_sum]`. Rewrite using `[Finset.sum_eq_single (⇑d)]`.

Establish `hind : d = Finsupp.indicator univ (fun i _ => d i)`. Use extensionality with `i`. Simplify using the standard rewrite rules. Rewrite using `[if_pos hind, mul_one]`. Establish `hspec` using `Nat.multinomial_spec (univ : Finset σ) (⇑d)`.

Rewrite `hspec` using `[hsum]`. Establish `hpos : (∏ i, ((d i).factorial : ℝ)) ≠ 0`. Rewrite using `[Finset.prod_ne_zero_iff]`. Introduce `i _`. Conclude with `(Nat.factorial_pos _).ne'` after adjusting the coercions.

Rewrite using `[Finset.prod_div_distrib, ← hspec]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Introduce `k _ hk`. Rewrite using `[if_neg, mul_zero]`.

Introduce `h`. Apply `hk` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Use `congrArg (fun f : σ →₀ ℕ => f i) h` as an intermediate fact. Simplify using `using this.symm`.

Introduce `h exfalso`. Apply `h` to reduce the goal to its premises. Rewrite using `[Finset.mem_piAntidiag]`. Conclude with `⟨hsum, fun i _ => Finset.mem_univ i⟩`.
-/
private theorem coeff_linearForm_pow_eq_factorial_mul_prod {σ : Type} [Fintype σ] [DecidableEq σ] (c : σ → ℝ) (n : ℕ)
    (d : σ →₀ ℕ) (hd : d.degree = n) :
    coeff d ((∑ x, C (c x) * X x) ^ n) =
      (n.factorial : ℝ) * ∏ x, (c x ^ d x / ((d x).factorial : ℝ)) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag, coeff_sum]
  simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod,
    ← map_natCast (C : ℝ →+* MvPolynomial σ ℝ), ← mul_assoc, ← map_mul, coeff_C_mul,
    coeff_prod_X_pow]
  have hsum : ∑ i, d i = n := by
    rw [← hd, Finsupp.degree_eq_sum]
  rw [Finset.sum_eq_single (⇑d)]
  · have hind : d = Finsupp.indicator univ (fun i _ => d i) := by
      ext i; simp
    rw [if_pos hind, mul_one]
    have hspec := Nat.multinomial_spec (univ : Finset σ) (⇑d)
    rw [hsum] at hspec
    have hpos : (∏ i, ((d i).factorial : ℝ)) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]; intro i _; exact_mod_cast (Nat.factorial_pos _).ne'
    rw [Finset.prod_div_distrib, ← hspec]
    push_cast
    field_simp
  · intro k _ hk
    rw [if_neg, mul_zero]
    intro h
    apply hk
    funext i
    have := congrArg (fun f : σ →₀ ℕ => f i) h
    simpa using this.symm
  · intro h
    exfalso; apply h
    rw [Finset.mem_piAntidiag]
    exact ⟨hsum, fun i _ => Finset.mem_univ i⟩

open MvPolynomial Finset in
/- English proof (translation)
Consider the cases of `N with`. Consider the case `zero => simp`. Consider the case `succ n`. Establish `h1 : ∏ i : Fin (n + 1), ∏ k ∈ Ioi i, (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) = (n.superFactorial : ℝ)`. Rewrite using `[← Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) n, Matrix.det_vandermonde]`.

Rewrite using `[h1, ← Nat.prod_range_succ_factorial, Nat.cast_prod, ← Fin.prod_univ_eq_prod_range (fun x => ((x.factorial : ℕ) : ℝ)) (n + 1)]`. Conclude with `Fintype.prod_equiv Fin.revPerm _ _ (fun j => rfl)`.
-/
private theorem prod_factorial_rev_eq_prod_sub (N : ℕ) :
    ∏ j : Fin N, ((j.rev : ℕ).factorial : ℝ) =
      ∏ i : Fin N, ∏ k ∈ Ioi i, (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by
  cases N with
  | zero => simp
  | succ n =>
    have h1 : ∏ i : Fin (n + 1), ∏ k ∈ Ioi i, (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) =
        (n.superFactorial : ℝ) := by
      rw [← Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) n, Matrix.det_vandermonde]
    rw [h1, ← Nat.prod_range_succ_factorial, Nat.cast_prod,
      ← Fin.prod_univ_eq_prod_range (fun x => ((x.factorial : ℕ) : ℝ)) (n + 1)]
    exact Fintype.prod_equiv Fin.revPerm _ _ (fun j => rfl)

open MvPolynomial Finset in
/- English proof (translation)
Establish `hrev : ∀ j : Fin N, N - 1 - (j : ℕ) = (j.rev : ℕ)`. Introduce `j`. Rewrite using `[Fin.val_rev]`. Use linear arithmetic over natural numbers and integers. Establish `hterm : ∀ π : Equiv.Perm (Fin N), ∏ i, (v i ^ (N - 1 - (π i : ℕ)) / ((N - 1 - (π i : ℕ)).factorial : ℝ)) = (∏ i, Matrix.transpose (Matrix.projVandermonde 1 v) (π i) i) * ∏ j : Fin N, (((j.rev : ℕ).factorial : ℝ))⁻¹`.

Introduce `π`. Repeatedly rewrite using `[div_eq_mul_inv, Finset.prod_mul_distrib, hrev]`. Use `congr 1`. Simplify using `[Matrix.projVandermonde_apply]`. Conclude with `Fintype.prod_equiv π _ _ (fun i => rfl)`.

Repeatedly rewrite using `[hterm, ← mul_assoc, ← Finset.sum_mul, ← Matrix.det_apply', Matrix.det_transpose, Matrix.det_projVandermonde, Finset.prod_inv_distrib, prod_factorial_rev_eq_prod_sub, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_div_distrib, div_eq_mul_inv]`. Simplify using `only [Pi.one_apply, one_mul]`. Rewrite using `[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]`.

Use `congr 1`. Use extensionality with `k`. Simplify using the standard rewrite rules.
-/
private theorem sum_sign_prod_pow_div_factorial_eq_prod {N : ℕ} (v : Fin N → ℝ) :
    ∑ π : Equiv.Perm (Fin N), ((Equiv.Perm.sign π : ℤ) : ℝ) *
        ∏ i, (v i ^ (N - 1 - (π i : ℕ)) / ((N - 1 - (π i : ℕ)).factorial : ℝ)) =
      ∏ i : Fin N, ∏ k : Fin N,
        if i < k then (v i - v k) / (((k : ℕ) : ℝ) - ((i : ℕ) : ℝ)) else 1 := by
  have hrev : ∀ j : Fin N, N - 1 - (j : ℕ) = (j.rev : ℕ) := by
    intro j; rw [Fin.val_rev]; omega
  have hterm : ∀ π : Equiv.Perm (Fin N),
      ∏ i, (v i ^ (N - 1 - (π i : ℕ)) / ((N - 1 - (π i : ℕ)).factorial : ℝ)) =
        (∏ i, Matrix.transpose (Matrix.projVandermonde 1 v) (π i) i) *
          ∏ j : Fin N, (((j.rev : ℕ).factorial : ℝ))⁻¹ := by
    intro π
    simp_rw [div_eq_mul_inv, Finset.prod_mul_distrib, hrev]
    congr 1
    · simp [Matrix.projVandermonde_apply]
    · exact Fintype.prod_equiv π _ _ (fun i => rfl)
  simp_rw [hterm, ← mul_assoc, ← Finset.sum_mul, ← Matrix.det_apply', Matrix.det_transpose,
    Matrix.det_projVandermonde, Finset.prod_inv_distrib, prod_factorial_rev_eq_prod_sub,
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_div_distrib, div_eq_mul_inv]
  simp only [Pi.one_apply, one_mul]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  congr 1
  ext k
  simp

open MvPolynomial Finset in

/- English proof (translation)
Unfold `_root_.Formalism.DegreeFormula.FlagDegFormula`. Introduce `ι _ _ N lam`. Unfold `_root_.Formalism.DegreeFormula.flagDeg _root_.Formalism.DegreeFormula.weylProd _root_.Formalism.DegreeFormula.linRoot`. Rewrite using `[neg_pow, ← map_one (C : ℝ →+* MvPolynomial (ι × Fin N) ℝ), ← map_neg, ← map_pow, _root_.Formalism.DegreeFormula.PPowSum.degFl_C_mul]`. Unfold `_root_.Formalism.DegreeFormula.degFl`.

Repeatedly rewrite using `[coeff_linearForm_pow_eq_factorial_mul_prod _ _ _ (_root_.Formalism.DegreeFormula.PPowSum.degree_permExp _)]`. Establish `hexp : ∀ (σ : ι → Equiv.Perm (Fin N)) (τ : ι) (i : Fin N), (_root_.Formalism.DegreeFormula.permExp σ) (τ, i) = N - 1 - ((σ τ) i : ℕ)`. Introduce `σ τ i`. Unfold `_root_.Formalism.DegreeFormula.permExp`. Both sides reduce to the same expression.

Repeatedly rewrite using `[Fintype.prod_prod_type, hexp]`. Rewrite using `[← Finset.prod_congr rfl (fun τ _ => sum_sign_prod_pow_div_factorial_eq_prod (lam τ)), Fintype.prod_sum]`. Rewrite using `[← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun σ _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.FlagPoly.flagDegFormula : _root_.Formalism.DegreeFormula.FlagDegFormula := by
  unfold _root_.Formalism.DegreeFormula.FlagDegFormula
  intro ι _ _ N lam
  unfold _root_.Formalism.DegreeFormula.flagDeg _root_.Formalism.DegreeFormula.weylProd _root_.Formalism.DegreeFormula.linRoot
  rw [neg_pow, ← map_one (C : ℝ →+* MvPolynomial (ι × Fin N) ℝ), ← map_neg, ← map_pow, _root_.Formalism.DegreeFormula.PPowSum.degFl_C_mul]
  unfold _root_.Formalism.DegreeFormula.degFl
  simp_rw [coeff_linearForm_pow_eq_factorial_mul_prod _ _ _ (_root_.Formalism.DegreeFormula.PPowSum.degree_permExp _)]
  have hexp : ∀ (σ : ι → Equiv.Perm (Fin N)) (τ : ι) (i : Fin N),
      (_root_.Formalism.DegreeFormula.permExp σ) (τ, i) = N - 1 - ((σ τ) i : ℕ) := by
    intro σ τ i
    unfold _root_.Formalism.DegreeFormula.permExp
    rfl
  simp_rw [Fintype.prod_prod_type, hexp]
  rw [← Finset.prod_congr rfl (fun τ _ => sum_sign_prod_pow_div_factorial_eq_prod (lam τ)),
    Fintype.prod_sum]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [Finset.prod_mul_distrib]
  ring

end GlobalTheory.FlagPoly
