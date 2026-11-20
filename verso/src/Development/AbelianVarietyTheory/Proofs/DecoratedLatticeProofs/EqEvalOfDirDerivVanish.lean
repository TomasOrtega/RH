import Mathlib
open scoped ContDiff

namespace GlobalTheory.PolyOfDeriv

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => intro G _ hN t`. Simplify using `[hN]`. Consider the case `succ N ih`. Introduce `G hG hN t`.

Establish `h1 : ∀ s, G 1 s = ∑ k ∈ Finset.range N, G (k+1) 0 * ((s ^ k / k.factorial : ℝ) : ℂ)` using `fun s => ih (fun k => G (k+1)) (fun k t => hG (k+1) t) hN s`. Establish `hm : ∀ (k : ℕ) (s : ℝ), HasDerivAt (fun s : ℝ => ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) ((s ^ k / k.factorial : ℝ) : ℂ) s`. Introduce `k s`. Establish `h` using `(hasDerivAt_pow (k+1) s).div_const ((k+1).factorial : ℝ)`. Establish `e : ((k+1 : ℕ) : ℝ) * s ^ (k + 1 - 1) / ((k+1).factorial : ℝ) = s ^ k / k.factorial`.

Rewrite using `[Nat.factorial_succ, Nat.add_sub_cancel, Nat.cast_mul]`. Establish `: ((k+1 : ℕ) : ℝ) ≠ 0` using `by positivity`. Establish `: ((k.factorial : ℕ) : ℝ) ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts. Rewrite `h` using `[e]`.

Conclude with `h.ofReal_comp`. Establish `hH : ∀ s, HasDerivAt (fun s => G 0 s - ∑ k ∈ Finset.range N, G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) 0 s`. Introduce `s`. Establish `h2 : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range N, G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) (G 1 s) s`. Rewrite using `[h1 s]`.

Conclude with `HasDerivAt.fun_sum fun k _ => (hm k s).const_mul _`. Establish `h3` using `(hG 0 s).fun_sub h2`. Rewrite `h3` using `[zero_add, sub_self]`. Then use the resulting hypothesis. Establish `hc` using `is_const_of_deriv_eq_zero (fun s => (hH s).differentiableAt) (fun s => (hH s).deriv) t 0`. Rewrite using `[Finset.sum_range_succ']`.

Simplify using `only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow, zero_div, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, sub_zero] at hc`. Rewrite using `[← hc]`. Simplify using the standard rewrite rules.
-/
theorem taylor_of_chain (N : ℕ) : ∀ (G : ℕ → ℝ → ℂ) (_ : ∀ k t, HasDerivAt (G k) (G (k+1) t) t)
    (_ : G N = 0) (t : ℝ),
    G 0 t = ∑ k ∈ Finset.range N, G k 0 * ((t ^ k / k.factorial : ℝ) : ℂ) := by
  induction N with
  | zero => intro G _ hN t; simp [hN]
  | succ N ih =>
    intro G hG hN t
    have h1 : ∀ s, G 1 s = ∑ k ∈ Finset.range N, G (k+1) 0 * ((s ^ k / k.factorial : ℝ) : ℂ) :=
      fun s => ih (fun k => G (k+1)) (fun k t => hG (k+1) t) hN s
    have hm : ∀ (k : ℕ) (s : ℝ), HasDerivAt
        (fun s : ℝ => ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ))
        ((s ^ k / k.factorial : ℝ) : ℂ) s := by
      intro k s
      have h := (hasDerivAt_pow (k+1) s).div_const ((k+1).factorial : ℝ)
      have e : ((k+1 : ℕ) : ℝ) * s ^ (k + 1 - 1) / ((k+1).factorial : ℝ) = s ^ k / k.factorial := by
        rw [Nat.factorial_succ, Nat.add_sub_cancel, Nat.cast_mul]
        have : ((k+1 : ℕ) : ℝ) ≠ 0 := by positivity
        have : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
        field_simp
      rw [e] at h
      exact h.ofReal_comp
    have hH : ∀ s, HasDerivAt (fun s => G 0 s - ∑ k ∈ Finset.range N,
        G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) 0 s := by
      intro s
      have h2 : HasDerivAt (fun s : ℝ => ∑ k ∈ Finset.range N,
          G (k+1) 0 * ((s ^ (k+1) / (k+1).factorial : ℝ) : ℂ)) (G 1 s) s := by
        rw [h1 s]
        exact HasDerivAt.fun_sum fun k _ => (hm k s).const_mul _
      have h3 := (hG 0 s).fun_sub h2
      rwa [zero_add, sub_self] at h3
    have hc := is_const_of_deriv_eq_zero (fun s => (hH s).differentiableAt)
      (fun s => (hH s).deriv) t 0
    rw [Finset.sum_range_succ']
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true, zero_pow,
      zero_div, Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, sub_zero] at hc
    rw [← hc]
    simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- English proof (translation)
Establish `hk : (k : WithTop ℕ∞) < ∞` using `by exact_mod_cast ENat.coe_lt_top k`. Establish `hd` using `((hu.differentiable_iteratedFDeriv hk) (y + t • x)).hasFDerivAt`. Establish `hl : HasDerivAt (fun t : ℝ => y + t • x) x t`. Simplify using `using ((hasDerivAt_id t).smul_const x).const_add y`. Establish `h1` using `hd.comp_hasDerivAt t hl`.

Establish `h2` using `(ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ (fun _ => x)).hasFDerivAt.comp_hasDerivAt t h1`. Rewrite using `[iteratedFDeriv_succ_apply_left]`. Conclude with `h2`.
-/
theorem hasDerivAt_iter {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (k : ℕ) (y x : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ k u (y + t • x) (fun _ => x))
      (iteratedFDeriv ℝ (k+1) u (y + t • x) (fun _ => x)) t := by
  have hk : (k : WithTop ℕ∞) < ∞ := by exact_mod_cast ENat.coe_lt_top k
  have hd := ((hu.differentiable_iteratedFDeriv hk) (y + t • x)).hasFDerivAt
  have hl : HasDerivAt (fun t : ℝ => y + t • x) x t := by
    simpa using ((hasDerivAt_id t).smul_const x).const_add y
  have h1 := hd.comp_hasDerivAt t hl
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℂ
    (fun _ => x)).hasFDerivAt.comp_hasDerivAt t h1
  rw [iteratedFDeriv_succ_apply_left]
  exact h2

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => funext y`. Simplify using the standard rewrite rules. Consider the case `succ k ih`. Rewrite using `[List.replicate_succ, List.foldr_cons, ih]`.

Use function extensionality and compare the values at `y`. Use `(hasDerivAt_iter hu k y x 0).deriv` as an intermediate fact. Simplify using `using this`.
-/
theorem foldr_replicate {u : E → ℂ} (hu : ContDiff ℝ ∞ u) (x : E) (k : ℕ) :
    (List.replicate k x).foldr
      (fun y g => fun z => deriv (fun t : ℝ => g (z + t • y)) 0) u
      = fun y => iteratedFDeriv ℝ k u y (fun _ => x) := by
  induction k with
  | zero => funext y; simp
  | succ k ih =>
    rw [List.replicate_succ, List.foldr_cons, ih]
    funext y
    have := (hasDerivAt_iter hu k y x 0).deriv
    simpa using this

/- English proof (translation)
Use `⟨∑ r : Fin k → ι, MvPolynomial.C (M (fun j => Pi.single (r j) (1:ℝ))) * ∏ j, MvPolynomial.X (r j), ?_⟩` and prove the remaining obligations. Introduce `x`. Establish `hx : (fun _ : Fin k => x) = fun _ => ∑ i, x i • (Pi.single i (1:ℝ) : ι → ℝ)`. Use function extensionality and compare the values at `_`. Use extensionality with `l`.

Simplify using `[Pi.single_apply]`. Rewrite using `[hx, M.map_sum]`. Simplify using `only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[M.map_smul_univ (fun j => x (r j)) (fun j => Pi.single (r j) 1)]`.

Rewrite using `[Complex.real_smul, Complex.ofReal_prod, mul_comm]`.
-/
theorem multilinear_diag_poly {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => ι → ℝ) ℂ) :
    ∃ q : MvPolynomial ι ℂ, ∀ x : ι → ℝ,
      M (fun _ => x) = MvPolynomial.eval (fun i => (x i : ℂ)) q := by
  refine ⟨∑ r : Fin k → ι, MvPolynomial.C (M (fun j => Pi.single (r j) (1:ℝ))) *
    ∏ j, MvPolynomial.X (r j), ?_⟩
  intro x
  have hx : (fun _ : Fin k => x) = fun _ => ∑ i, x i • (Pi.single i (1:ℝ) : ι → ℝ) := by
    funext _; ext l; simp [Pi.single_apply]
  rw [hx, M.map_sum]
  simp only [map_sum, map_mul, MvPolynomial.eval_C, map_prod, MvPolynomial.eval_X]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [M.map_smul_univ (fun j => x (r j)) (fun j => Pi.single (r j) 1)]
  rw [Complex.real_smul, Complex.ofReal_prod, mul_comm]

/- English proof (translation)
Introduce `ι _ _ N u hu hL`. Use `choose q hq using fun k => multilinear_diag_poly (iteratedFDeriv ℝ k u 0)`. Use `⟨∑ k ∈ Finset.range N, MvPolynomial.C ((k.factorial : ℂ)⁻¹) * q k, ?_⟩` and prove the remaining obligations. Introduce `x`. Establish `hrep` using `hL (List.replicate N x) List.length_replicate`.

Rewrite `hrep` using `[foldr_replicate hu]`. Establish `key` using `taylor_of_chain N (fun k t => iteratedFDeriv ℝ k u (0 + t • x) (fun _ => x)) (fun k t => hasDerivAt_iter hu k 0 x t) (by funext t; exact congrFun hrep _) 1`. Simplify using `only [zero_add, one_smul, zero_smul, iteratedFDeriv_zero_apply, hq] at key`. Rewrite using `[key]`. Simplify using `only [map_sum, map_mul, MvPolynomial.eval_C]`.

Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Simplify using the standard rewrite rules.
-/
theorem eq_eval_of_dirDeriv_vanish : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ)
    (u : (ι → ℝ) → ℂ), ContDiff ℝ ∞ u →
    (∀ L : List (ι → ℝ), L.length = N →
      L.foldr (fun y g => fun x => deriv (fun t : ℝ => g (x + t • y)) 0) u = 0) →
    ∃ p : MvPolynomial ι ℂ, ∀ x, u x = MvPolynomial.eval (fun i => (x i : ℂ)) p := by
  intro ι _ _ N u hu hL
  choose q hq using fun k => multilinear_diag_poly (iteratedFDeriv ℝ k u 0)
  refine ⟨∑ k ∈ Finset.range N, MvPolynomial.C ((k.factorial : ℂ)⁻¹) * q k, ?_⟩
  intro x
  have hrep := hL (List.replicate N x) List.length_replicate
  rw [foldr_replicate hu] at hrep
  have key := taylor_of_chain N (fun k t => iteratedFDeriv ℝ k u (0 + t • x) (fun _ => x))
    (fun k t => hasDerivAt_iter hu k 0 x t) (by funext t; exact congrFun hrep _) 1
  simp only [zero_add, one_smul, zero_smul, iteratedFDeriv_zero_apply, hq] at key
  rw [key]
  simp only [map_sum, map_mul, MvPolynomial.eval_C]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comm]; simp

end GlobalTheory.PolyOfDeriv
