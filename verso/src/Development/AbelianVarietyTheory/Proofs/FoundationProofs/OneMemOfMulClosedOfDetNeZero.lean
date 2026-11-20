import Mathlib
open scoped Matrix
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `F K _ _ _ _ m S hS T hT hdet`. Establish `hTu : IsUnit T` using `(Matrix.isUnit_iff_isUnit_det T).2 (isUnit_iff_ne_zero.2 hdet)`. Establish `hint : IsIntegral F T`. Establish `hK : IsIntegral K T` using `Algebra.IsIntegral.isIntegral T`. Conclude with `isIntegral_trans T hK`.

Establish `hpow : ∀ n : ℕ, T ^ (n + 1) ∈ S`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simpa using hT`. Consider the case `succ n ih => rw [pow_succ]`.

Conclude with `hS _ ih _ hT`. Establish `hmul : ∀ q : F[X], T * aeval T q ∈ S`. Introduce `q`. Rewrite using `[aeval_eq_sum_range, Finset.mul_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_smul_comm, ← pow_succ']`. Conclude with `S.smul_mem _ (hpow i)`. Use `set p := minpoly F T with hpdef`. Establish `hp0 : p ≠ 0` using `minpoly.ne_zero hint`. Establish `hkey : T * aeval T p.divX + algebraMap F _ (p.coeff 0) = 0`.

Establish `h0 : aeval T p = 0` using `minpoly.aeval F T`. Establish `e : aeval T p = T * aeval T p.divX + algebraMap F _ (p.coeff 0)` using `by conv_lhs => rw [← divX_mul_X_add p, mul_comm p.divX X]`. Simplify using `only [map_add, map_mul, aeval_X, aeval_C]`. Rewrite using `[← e, h0]`. Establish `hc : p.coeff 0 ≠ 0`.

Introduce `hc`. Rewrite `hkey` using `[hc, map_zero, add_zero]`. Establish `hq : aeval T p.divX = 0`. Conclude with `hTu.mul_right_eq_zero.1 hkey`. Establish `hne : p.divX ≠ 0`.

Introduce `h`. Rewrite `h` using `[divX_eq_zero_iff, hc, map_zero]`. Conclude with `hp0 h`. Establish `hle` using `minpoly.degree_le_of_ne_zero F T hne hq`. Conclude with `absurd (degree_divX_lt hp0) (not_lt.2 hle)`.

Establish `hone : (1 : Matrix (Fin m) (Fin m) K) = (-(p.coeff 0)⁻¹) • (T * aeval T p.divX)`. Rewrite using `[eq_neg_of_add_eq_zero_left hkey, smul_neg, neg_smul, neg_neg, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc, map_one]`. Rewrite using `[hone]`. Conclude with `S.smul_mem _ (hmul _)`.
-/
theorem one_mem_of_mulClosed_of_det_ne_zero : ∀ {F K : Type} [Field F] [Field K] [Algebra F K]
    [Algebra.IsIntegral F K] {m : ℕ} (S : Submodule F (Matrix (Fin m) (Fin m) K)),
    (∀ x ∈ S, ∀ y ∈ S, x * y ∈ S) → ∀ T ∈ S, T.det ≠ 0 → (1 : Matrix (Fin m) (Fin m) K) ∈ S := by
  intro F K _ _ _ _ m S hS T hT hdet
  classical
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).2 (isUnit_iff_ne_zero.2 hdet)
  have hint : IsIntegral F T := by
    have hK : IsIntegral K T := Algebra.IsIntegral.isIntegral T
    exact isIntegral_trans T hK
  have hpow : ∀ n : ℕ, T ^ (n + 1) ∈ S := by
    intro n
    induction n with
    | zero => simpa using hT
    | succ n ih => rw [pow_succ]; exact hS _ ih _ hT
  have hmul : ∀ q : F[X], T * aeval T q ∈ S := by
    intro q
    rw [aeval_eq_sum_range, Finset.mul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_smul_comm, ← pow_succ']
    exact S.smul_mem _ (hpow i)
  set p := minpoly F T with hpdef
  have hp0 : p ≠ 0 := minpoly.ne_zero hint
  have hkey : T * aeval T p.divX + algebraMap F _ (p.coeff 0) = 0 := by
    have h0 : aeval T p = 0 := minpoly.aeval F T
    have e : aeval T p = T * aeval T p.divX + algebraMap F _ (p.coeff 0) := by
      conv_lhs => rw [← divX_mul_X_add p, mul_comm p.divX X]
      simp only [map_add, map_mul, aeval_X, aeval_C]
    rw [← e, h0]
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    rw [hc, map_zero, add_zero] at hkey
    have hq : aeval T p.divX = 0 := by
      exact hTu.mul_right_eq_zero.1 hkey
    have hne : p.divX ≠ 0 := by
      intro h
      rw [divX_eq_zero_iff, hc, map_zero] at h
      exact hp0 h
    have hle := minpoly.degree_le_of_ne_zero F T hne hq
    exact absurd (degree_divX_lt hp0) (not_lt.2 hle)
  have hone : (1 : Matrix (Fin m) (Fin m) K) = (-(p.coeff 0)⁻¹) • (T * aeval T p.divX) := by
    rw [eq_neg_of_add_eq_zero_left hkey, smul_neg, neg_smul, neg_neg, Algebra.smul_def,
      ← map_mul, inv_mul_cancel₀ hc, map_one]
  rw [hone]
  exact S.smul_mem _ (hmul _)

end GlobalTheory
