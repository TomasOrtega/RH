import Mathlib
import Formalism.PeriodIntegrals.ScalDeg

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScalDeg

open MvPolynomial PI.ScalDeg

open Classical in

/- English proof (translation)
Unfold `Finsupp.prod Finsupp.sum`. Repeatedly rewrite using `[← Finset.prod_pow_eq_pow_sum]`. Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [pow_ite, pow_zero]`.

Rewrite using `[Finset.prod_ite_eq]`. Simplify using the standard rewrite rules.
-/
theorem prod_fiber {T : Type} [Fintype T] {N : ℕ} (s : T → ℂ) (v : FrV T N →₀ ℕ) :
    (v.prod fun k n => s k.1 ^ n) =
      ∏ τ, s τ ^ (v.sum fun k n => if k.1 = τ then n else 0) := by
  unfold Finsupp.prod Finsupp.sum
  simp_rw [← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [pow_ite, pow_zero]
  rw [Finset.prod_ite_eq]
  simp

def gv {T : Type} {N N' : ℕ} (s : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ) (k : FrV T N) :
    MvPolynomial (Idx T N N') ℂ :=
  ∑ b : Fin N', C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
    X ((k.1, b, k.2.1) : Idx T N N')

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem polD_eq {T : Type} {N N' : ℕ} (s : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (y' : T → Matrix (Fin N') (Fin N') ℂ) : polD s Q y' = aeval (gv s y') Q := rfl

/- English proof (translation)
Unfold `gv`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_assoc, ← C_mul, mul_assoc]`.
-/
theorem gv_mul {T : Type} {N N' : ℕ} (s s' : T → ℂ) (y' : T → Matrix (Fin N') (Fin N') ℂ)
    (k : FrV T N) : gv (fun τ => s τ * s' τ) y' k = C (s k.1) * gv s' y' k := by
  unfold gv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← mul_assoc, ← C_mul, mul_assoc]

/- English proof (translation)
Rewrite using `[polD_eq, polD_eq]`. Unfold `sclP`. Rewrite using `[← AlgHom.comp_apply, MvPolynomial.comp_aeval]`. Use `congr 2`. Use function extensionality and compare the values at `k`.

Rewrite using `[gv_mul]`. Unfold `gv`. Rewrite using `[map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, aeval_C, aeval_X, algebraMap_eq]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem part_two {T : Type} {N N' : ℕ} (s s' : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (y' : T → Matrix (Fin N') (Fin N') ℂ) :
    sclP s (polD s' Q y') = polD (fun τ => s τ * s' τ) Q y' := by
  rw [polD_eq, polD_eq]
  unfold sclP
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 2
  funext k
  rw [gv_mul]
  unfold gv
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, aeval_C, aeval_X, algebraMap_eq]
  ring

open Classical in
/- English proof (translation)
Rewrite using `[polD_eq, polD_eq]`. Use `conv_lhs => rw [MvPolynomial.as_sum Q]`. Use `conv_rhs => rw [MvPolynomial.as_sum Q]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun v hv => ?_` and prove the remaining obligations.

Rewrite using `[aeval_monomial, aeval_monomial]`. Establish `hg : (v.prod fun i k => gv (fun τ => s τ * s' τ) y' i ^ k) = C (v.prod fun i k => s i.1 ^ k) * v.prod fun i k => gv s' y' i ^ k`. Repeatedly rewrite using `[gv_mul, mul_pow]`. Rewrite using `[Finsupp.prod_mul]`. Use `congr 1`.

Rewrite using `[map_finsuppProd]`. Repeatedly rewrite using `[map_pow]`. Establish `hp : (v.prod fun i k => s i.1 ^ k) = ∏ τ, s τ ^ dg τ`. Rewrite using `[prod_fiber]`. Conclude with `Finset.prod_congr rfl fun τ _ => by rw [hQ v hv τ]`.

Rewrite using `[hg, hp]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem part_one {T : Type} [Fintype T] {N N' : ℕ} (s s' : T → ℂ) (Q : MvPolynomial (FrV T N) ℂ)
    (dg : T → ℕ) (hQ : HomDeg Q dg) (y' : T → Matrix (Fin N') (Fin N') ℂ) :
    polD (fun τ => s τ * s' τ) Q y' = C (∏ τ, s τ ^ dg τ) * polD s' Q y' := by
  rw [polD_eq, polD_eq]
  conv_lhs => rw [MvPolynomial.as_sum Q]
  conv_rhs => rw [MvPolynomial.as_sum Q]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [aeval_monomial, aeval_monomial]
  have hg : (v.prod fun i k => gv (fun τ => s τ * s' τ) y' i ^ k) =
      C (v.prod fun i k => s i.1 ^ k) * v.prod fun i k => gv s' y' i ^ k := by
    simp_rw [gv_mul, mul_pow]
    rw [Finsupp.prod_mul]
    congr 1
    rw [map_finsuppProd]
    simp_rw [map_pow]
  have hp : (v.prod fun i k => s i.1 ^ k) = ∏ τ, s τ ^ dg τ := by
    rw [prod_fiber]
    exact Finset.prod_congr rfl fun τ _ => by rw [hQ v hv τ]
  rw [hg, hp]
  ring

/- English proof (translation)
Introduce `T _ N N' s s' Q dg hQ y'`. Conclude with `⟨part_one s s' Q dg hQ y', part_two s s' Q y'⟩`.
-/
theorem scalDeg_main : PI.ScalDeg.ScalDeg := by
  intro T _ N N' s s' Q dg hQ y'
  exact ⟨part_one s s' Q dg hQ y', part_two s s' Q y'⟩

end PI.UnitaryGroupMassFormula.ScalDeg
