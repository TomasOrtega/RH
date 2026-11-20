import Mathlib
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder

namespace GlobalTheory.LOneLower

/- English proof (translation)
Establish `key : ∀ N, ‖∑ n ∈ Finset.range N, a n * (b n : ℂ) - (∑ n ∈ Finset.range N, a n) * (b N : ℂ)‖ ≤ M * (b 0 - b N)`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`.

Establish `e : ∑ n ∈ Finset.range (N+1), a n * (b n : ℂ) - (∑ n ∈ Finset.range (N+1), a n) * (b (N+1) : ℂ) = (∑ n ∈ Finset.range N, a n * (b n : ℂ) - (∑ n ∈ Finset.range N, a n) * (b N : ℂ)) + (∑ n ∈ Finset.range (N+1), a n) * ((b N - b (N+1) : ℝ) : ℂ)`. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Establish `h1 : 0 ≤ b N - b (N+1)` using `sub_nonneg.2 (hb (Nat.le_succ N))`. Establish `h2 : ‖(∑ n ∈ Finset.range (N+1), a n) * ((b N - b (N+1) : ℝ) : ℂ)‖ ≤ M * (b N - b (N+1))`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg h1]`. Conclude with `mul_le_mul_of_nonneg_right (hA _) h1`. Use `norm_add_le (∑ n ∈ Finset.range N, a n * (b n : ℂ) - (∑ n ∈ Finset.range N, a n) * (b N : ℂ)) ((∑ n ∈ Finset.range (N+1), a n) * ((b N - b (N+1) : ℝ) : ℂ))` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ‖(∑ n ∈ Finset.range N, a n) * (b N : ℂ)‖ ≤ M * b N`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_of_nonneg (hb0 N)]`. Conclude with `mul_le_mul_of_nonneg_right (hA _) (hb0 N)`. Establish `h3` using `norm_sub_norm_le (∑ n ∈ Finset.range N, a n * (b n : ℂ)) ((∑ n ∈ Finset.range N, a n) * (b N : ℂ))`.

Use `key N` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem abel_bound (a : ℕ → ℂ) (b : ℕ → ℝ) (M : ℝ) (hA : ∀ N, ‖∑ n ∈ Finset.range N, a n‖ ≤ M)
    (hb : Antitone b) (hb0 : ∀ n, 0 ≤ b n) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, a n * (b n : ℂ)‖ ≤ M * b 0 := by
  have key : ∀ N, ‖∑ n ∈ Finset.range N, a n * (b n : ℂ)
      - (∑ n ∈ Finset.range N, a n) * (b N : ℂ)‖ ≤ M * (b 0 - b N) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have e : ∑ n ∈ Finset.range (N+1), a n * (b n : ℂ)
          - (∑ n ∈ Finset.range (N+1), a n) * (b (N+1) : ℂ)
          = (∑ n ∈ Finset.range N, a n * (b n : ℂ) - (∑ n ∈ Finset.range N, a n) * (b N : ℂ))
            + (∑ n ∈ Finset.range (N+1), a n) * ((b N - b (N+1) : ℝ) : ℂ) := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
        push_cast
        ring
      rw [e]
      have h1 : 0 ≤ b N - b (N+1) := sub_nonneg.2 (hb (Nat.le_succ N))
      have h2 : ‖(∑ n ∈ Finset.range (N+1), a n) * ((b N - b (N+1) : ℝ) : ℂ)‖
          ≤ M * (b N - b (N+1)) := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h1]
        exact mul_le_mul_of_nonneg_right (hA _) h1
      have := norm_add_le (∑ n ∈ Finset.range N, a n * (b n : ℂ)
        - (∑ n ∈ Finset.range N, a n) * (b N : ℂ))
        ((∑ n ∈ Finset.range (N+1), a n) * ((b N - b (N+1) : ℝ) : ℂ))
      linarith
  have h2 : ‖(∑ n ∈ Finset.range N, a n) * (b N : ℂ)‖ ≤ M * b N := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hb0 N)]
    exact mul_le_mul_of_nonneg_right (hA _) (hb0 N)
  have h3 := norm_sub_norm_le (∑ n ∈ Finset.range N, a n * (b n : ℂ))
    ((∑ n ∈ Finset.range N, a n) * (b N : ℂ))
  have := key N
  linarith

/- English proof (translation)
Establish `h0 : ∑ n ∈ Finset.range q, χ (n : ZMod q) = 0`. Rewrite using `[← MulChar.sum_eq_zero_of_ne_one hχ]`. Use `Finset.sum_nbij' (fun n => (n : ZMod q)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a _`.

Simplify using `using ZMod.val_lt a`. Introduce `n hn`. Conclude with `ZMod.val_cast_of_lt (by simpa using hn)`. Introduce `a _`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish `h1 : ∑ n ∈ Finset.range q, χ ((n + 1 : ℕ) : ZMod q) = 0`. Establish `e1` using `Finset.sum_range_succ (fun n : ℕ => χ (n : ZMod q)) q`. Establish `e2` using `Finset.sum_range_succ' (fun n : ℕ => χ (n : ZMod q)) q`. Rewrite `e2` using `[e1, h0]`.

Simplify using `only [ZMod.natCast_self, Nat.cast_zero, zero_add] at e2`. Conclude with `left_eq_add.1 (by rw [add_comm]; exact e2)`. Establish `h2 : ∀ N, ∑ n ∈ Finset.range (q + N), χ ((n + 1 : ℕ) : ZMod q) = ∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q)`. Introduce `N`. Rewrite using `[Finset.sum_range_add, h1, zero_add]`.

Simplify using the standard rewrite rules. Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Distinguish the cases in `h : N ≤ q`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Use `(Finset.sum_le_sum fun n _ => χ.norm_le_one _).trans ?_` and prove the remaining obligations. Simplify using `using h`. Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le (not_le.1 h).le`. Rewrite using `[h2]`. Conclude with `ih k (by have := NeZero.pos q; omega)`.
-/
theorem char_sum_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q)‖ ≤ q := by
  have h0 : ∑ n ∈ Finset.range q, χ (n : ZMod q) = 0 := by
    rw [← MulChar.sum_eq_zero_of_ne_one hχ]
    refine Finset.sum_nbij' (fun n => (n : ZMod q)) (fun a => a.val) ?_ ?_ ?_ ?_ ?_
    · simp
    · intro a _
      simpa using ZMod.val_lt a
    · intro n hn
      exact ZMod.val_cast_of_lt (by simpa using hn)
    · intro a _
      simp
    · simp
  have h1 : ∑ n ∈ Finset.range q, χ ((n + 1 : ℕ) : ZMod q) = 0 := by
    have e1 := Finset.sum_range_succ (fun n : ℕ => χ (n : ZMod q)) q
    have e2 := Finset.sum_range_succ' (fun n : ℕ => χ (n : ZMod q)) q
    rw [e1, h0] at e2
    simp only [ZMod.natCast_self, Nat.cast_zero, zero_add] at e2
    exact left_eq_add.1 (by rw [add_comm]; exact e2)
  have h2 : ∀ N, ∑ n ∈ Finset.range (q + N), χ ((n + 1 : ℕ) : ZMod q)
      = ∑ n ∈ Finset.range N, χ ((n + 1 : ℕ) : ZMod q) := by
    intro N
    rw [Finset.sum_range_add, h1, zero_add]
    simp
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases h : N ≤ q
    · refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun n _ => χ.norm_le_one _).trans ?_
      simpa using h
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_le.1 h).le
      rw [h2]
      exact ih k (by have := NeZero.pos q; omega)

noncomputable def wt (x : ℝ) : ℝ := x⁻¹ - (Real.exp x - 1)⁻¹

/- English proof (translation)
Use `Real.add_one_le_exp x` as an intermediate fact. Conclude with `sub_nonneg.2 (inv_anti₀ hx (by linarith))`.
-/
theorem wt_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ wt x := by
  have := Real.add_one_le_exp x
  exact sub_nonneg.2 (inv_anti₀ hx (by linarith))

/- English proof (translation)
Establish `h1` using `Real.add_one_le_exp x`. Establish `h2` using `Real.add_one_le_exp (-x)`. Establish `h3 : Real.exp x * Real.exp (-x) = 1` using `by rw [← Real.exp_add]; simp`. Establish `h4` using `Real.exp_pos x`. Establish `h5 : 0 < Real.exp x - 1` using `by linarith`.

Unfold `wt`. Rewrite using `[inv_sub_inv hx.ne' h5.ne', div_le_one (by positivity)]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem wt_le_one {x : ℝ} (hx : 0 < x) : wt x ≤ 1 := by
  have h1 := Real.add_one_le_exp x
  have h2 := Real.add_one_le_exp (-x)
  have h3 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have h4 := Real.exp_pos x
  have h5 : 0 < Real.exp x - 1 := by linarith
  unfold wt
  rw [inv_sub_inv hx.ne' h5.ne', div_le_one (by positivity)]
  nlinarith

/- English proof (translation)
Establish `hd : ∀ x : ℝ, 0 < x → HasDerivAt wt (-(x ^ 2)⁻¹ - (-Real.exp x / (Real.exp x - 1) ^ 2)) x`. Introduce `x hx`. Establish `h5 : 0 < Real.exp x - 1` using `by linarith [Real.add_one_le_exp x]`. Conclude with `(hasDerivAt_inv hx.ne').sub (((Real.hasDerivAt_exp x).sub_const 1).inv h5.ne')`. Use `antitoneOn_of_deriv_nonpos (convex_Ioi 0) (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_ ?_` and prove the remaining obligations.

Introduce `x hx`. Rewrite `hx` using `[interior_Ioi]`. Conclude with `(hd x hx).differentiableAt.differentiableWithinAt`. Introduce `x hx`. Rewrite `hx` using `[interior_Ioi]`.

Establish `hx' : 0 < x` using `hx`. Rewrite using `[(hd x hx).deriv]`. Establish `h5 : 0 < Real.exp x - 1` using `by linarith [Real.add_one_le_exp x]`. Establish `h6 : x / 2 ≤ Real.sinh (x / 2)` using `Real.self_le_sinh_iff.2 (by linarith)`. Rewrite `h6` using `[Real.sinh_eq]`.

Establish `h7 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1` using `by rw [← Real.exp_add]; simp`. Establish `h8 : Real.exp x = Real.exp (x / 2) ^ 2` using `by rw [sq, ← Real.exp_add]; simp`. Establish `h9` using `Real.exp_pos (x / 2)`. Establish `h10 : x * Real.exp (x / 2) ≤ Real.exp x - 1` using `by rw [h8]; nlinarith`. Establish `h11 : (x * Real.exp (x / 2)) ^ 2 ≤ (Real.exp x - 1) ^ 2` using `by gcongr`.

Rewrite `h11` using `[mul_pow, ← h8]`. Establish `: Real.exp x / (Real.exp x - 1) ^ 2 ≤ (x ^ 2)⁻¹`. Rewrite using `[div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[neg_div]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem wt_antitoneOn : AntitoneOn wt (Set.Ioi 0) := by
  have hd : ∀ x : ℝ, 0 < x → HasDerivAt wt (-(x ^ 2)⁻¹ - (-Real.exp x / (Real.exp x - 1) ^ 2)) x := by
    intro x hx
    have h5 : 0 < Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    exact (hasDerivAt_inv hx.ne').sub (((Real.hasDerivAt_exp x).sub_const 1).inv h5.ne')
  refine antitoneOn_of_deriv_nonpos (convex_Ioi 0)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) ?_ ?_
  · intro x hx
    rw [interior_Ioi] at hx
    exact (hd x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hx' : 0 < x := hx
    rw [(hd x hx).deriv]
    have h5 : 0 < Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    have h6 : x / 2 ≤ Real.sinh (x / 2) := Real.self_le_sinh_iff.2 (by linarith)
    rw [Real.sinh_eq] at h6
    have h7 : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by rw [← Real.exp_add]; simp
    have h8 : Real.exp x = Real.exp (x / 2) ^ 2 := by rw [sq, ← Real.exp_add]; simp
    have h9 := Real.exp_pos (x / 2)
    have h10 : x * Real.exp (x / 2) ≤ Real.exp x - 1 := by rw [h8]; nlinarith
    have h11 : (x * Real.exp (x / 2)) ^ 2 ≤ (Real.exp x - 1) ^ 2 := by gcongr
    rw [mul_pow, ← h8] at h11
    have : Real.exp x / (Real.exp x - 1) ^ 2 ≤ (x ^ 2)⁻¹ := by
      rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
      linarith
    rw [neg_div]
    linarith

/- English proof (translation)
Establish `hp : ∀ p k : ℕ, p.Prime → 1 ≤ zetaMul χ (p ^ (2 * k))`. Introduce `p k hp`. Rewrite using `[zetaMul, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]`. Simplify using `only [toArithmeticFunction, coe_mk, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte, Nat.cast_pow, map_pow]`. Break down `MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h` into its components or cases.

Rewrite using `[Finset.sum_range_succ', pow_zero]`. Conclude with `le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => by simp [h])`. Rewrite using `[Finset.sum_range_succ', pow_zero]`. Conclude with `le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => by simp [h])`. Simplify using `[h, neg_one_geom_sum]`.

Rewrite using `[χ.isMultiplicative_zetaMul.multiplicative_factorization _ (pow_ne_zero 2 hm)]`. Use `Finset.prod_induction _ (fun z : ℂ => 1 ≤ z) (fun a b ha hb => ?_) le_rfl fun p hp' => ?_` and prove the remaining obligations. Conclude with `one_le_mul_of_one_le_of_one_le ha hb`. Use `hp p (m.factorization p) (Nat.prime_of_mem_primeFactors hp')` as an intermediate fact. Simplify `this` using `[Nat.factorization_pow]`.
-/
theorem one_le_zetaMul_sq {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) {m : ℕ}
    (hm : m ≠ 0) : 1 ≤ zetaMul χ (m ^ 2) := by
  have hp : ∀ p k : ℕ, p.Prime → 1 ≤ zetaMul χ (p ^ (2 * k)) := by
    intro p k hp
    rw [zetaMul, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    simp only [toArithmeticFunction, coe_mk, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
      Nat.cast_pow, map_pow]
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
    · rw [Finset.sum_range_succ', pow_zero]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => by simp [h])
    · rw [Finset.sum_range_succ', pow_zero]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun i _ => by simp [h])
    · simp [h, neg_one_geom_sum]
  rw [χ.isMultiplicative_zetaMul.multiplicative_factorization _ (pow_ne_zero 2 hm)]
  refine Finset.prod_induction _ (fun z : ℂ => 1 ≤ z) (fun a b ha hb => ?_) le_rfl fun p hp' => ?_
  · exact one_le_mul_of_one_le_of_one_le ha hb
  · have := hp p (m.factorization p) (Nat.prime_of_mem_primeFactors hp')
    simpa [Nat.factorization_pow] using this

/- English proof (translation)
Establish `hs : Summable fun c : ℕ+ × ℕ+ => χ ((c.1 : ℕ) : ZMod q) * t ^ (c.1 * c.2 : ℕ)`. Use `Summable.of_norm_bounded (summable_prod_mul_pow 0 ht).norm fun c => ?_` and prove the remaining obligations. Rewrite using `[pow_zero, one_mul, norm_mul]`. Conclude with `mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)`. Establish `e : ∑' d : ℕ+, χ ((d : ℕ) : ZMod q) * (t ^ (d : ℕ) / (1 - t ^ (d : ℕ))) = ∑' c : ℕ+ × ℕ+, χ ((c.1 : ℕ) : ZMod q) * t ^ (c.1 * c.2 : ℕ)`.

Rewrite using `[hs.tsum_prod]`. Use `tsum_congr fun d => ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[tsum_mul_left]`. Use `congr 1`.

Establish `h1 : ‖t ^ (d : ℕ)‖ < 1`. Rewrite using `[norm_pow]`. Conclude with `pow_lt_one₀ (norm_nonneg _) ht d.ne_zero`. Simplify using `only [pow_mul]`. Rewrite using `[tsum_pnat_eq_tsum_succ (f := fun m => (t ^ (d : ℕ)) ^ m)]`.

Simplify using `only [pow_succ']`. Rewrite using `[tsum_mul_left, tsum_geometric_of_norm_lt_one h1, div_eq_mul_inv]`. Rewrite using `[e]`. Establish `h2` using `sigmaAntidiagonalEquivProd.hasSum_iff.2 hs.hasSum`. Use `h2.sigma fun n => ?_` and prove the remaining obligations.

Use `(congrArg (HasSum _) ?_).mpr (hasSum_fintype _)` and prove the remaining obligations. Simplify using `only [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors, PNat.mk_coe, Equiv.coe_fn_mk, Finset.univ_eq_attach]`. Rewrite using `[(n : ℕ).divisorsAntidiagonal.sum_attach (fun x : ℕ × ℕ => χ ((x.1 : ℕ) : ZMod q) * t ^ (x.1 * x.2)), Nat.sum_divisorsAntidiagonal (fun x y => χ ((x : ℕ) : ZMod q) * t ^ (x * y)), zetaMul, coe_zeta_mul_apply, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hi)]`.

Simplify using `[toArithmeticFunction, (Nat.pos_of_mem_divisors hi).ne']`.
-/
theorem lambert {q : ℕ} (χ : DirichletCharacter ℂ q) {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ+ => zetaMul χ n * t ^ (n : ℕ))
      (∑' d : ℕ+, χ ((d : ℕ) : ZMod q) * (t ^ (d : ℕ) / (1 - t ^ (d : ℕ)))) := by
  have hs : Summable fun c : ℕ+ × ℕ+ => χ ((c.1 : ℕ) : ZMod q) * t ^ (c.1 * c.2 : ℕ) := by
    refine Summable.of_norm_bounded (summable_prod_mul_pow 0 ht).norm fun c => ?_
    rw [pow_zero, one_mul, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  have e : ∑' d : ℕ+, χ ((d : ℕ) : ZMod q) * (t ^ (d : ℕ) / (1 - t ^ (d : ℕ)))
      = ∑' c : ℕ+ × ℕ+, χ ((c.1 : ℕ) : ZMod q) * t ^ (c.1 * c.2 : ℕ) := by
    rw [hs.tsum_prod]
    refine tsum_congr fun d => ?_
    simp only
    rw [tsum_mul_left]
    congr 1
    have h1 : ‖t ^ (d : ℕ)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) ht d.ne_zero
    simp only [pow_mul]
    rw [tsum_pnat_eq_tsum_succ (f := fun m => (t ^ (d : ℕ)) ^ m)]
    simp only [pow_succ']
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one h1, div_eq_mul_inv]
  rw [e]
  have h2 := sigmaAntidiagonalEquivProd.hasSum_iff.2 hs.hasSum
  refine h2.sigma fun n => ?_
  refine (congrArg (HasSum _) ?_).mpr (hasSum_fintype _)
  simp only [Function.comp, sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors,
    PNat.mk_coe, Equiv.coe_fn_mk, Finset.univ_eq_attach]
  rw [(n : ℕ).divisorsAntidiagonal.sum_attach
    (fun x : ℕ × ℕ => χ ((x.1 : ℕ) : ZMod q) * t ^ (x.1 * x.2)),
    Nat.sum_divisorsAntidiagonal (fun x y => χ ((x : ℕ) : ZMod q) * t ^ (x * y)),
    zetaMul, coe_zeta_mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hi)]
  simp [toArithmeticFunction, (Nat.pos_of_mem_divisors hi).ne']

/- English proof (translation)
Use `set α : ℝ := ((M : ℝ) ^ 2)⁻¹ with hα`. Establish `hα0 : 0 < α` using `by positivity`. Use `set t : ℝ := Real.exp (-α) with ht`. Establish `ht0 : 0 < t` using `Real.exp_pos _`. Establish `ht1 : t < 1` using `Real.exp_lt_one_iff.2 (by linarith)`.

Establish `hn : ‖(t : ℂ)‖ < 1` using `by rwa [Complex.norm_real, Real.norm_of_nonneg ht0.le]`. Establish `h1` using `lambert χ hn`. Rewrite `h1` using `[tsum_pnat_eq_tsum_succ (f := fun d : ℕ => χ (d : ZMod q) * ((t : ℂ) ^ d / (1 - (t : ℂ) ^ d)))]`. Establish `e : ∀ d : ℕ, (((Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ) : ℂ) = (t : ℂ) ^ (d + 1) / (1 - (t : ℂ) ^ (d + 1))`. Introduce `d`.

Establish `: t ^ (d + 1) = (Real.exp (((d + 1 : ℕ) : ℝ) * α))⁻¹`. Rewrite using `[ht, ← Real.exp_nat_mul, ← Real.exp_neg, mul_neg]`. Establish `h2 : (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ = t ^ (d + 1) / (1 - t ^ (d + 1))`. Rewrite using `[this]`. Establish `h3 : 0 < ((d + 1 : ℕ) : ℝ) * α` using `by positivity`.

Establish `h4` using `Real.add_one_le_exp (((d + 1 : ℕ) : ℝ) * α)`. Generalize the expression as in `Real.exp (((d + 1 : ℕ) : ℝ) * α) = E at *`. Establish `h5 : E - 1 ≠ 0` using `by linarith`. Establish `h6 : E ≠ 0` using `by linarith`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[h2]`. Use `push_cast`. Both sides reduce to the same expression. Simplify using `only [e]`. Use `le_trans ?_ (Complex.re_le_norm _)` and prove the remaining obligations.

Establish `h3` using `Complex.hasSum_re h1`. Establish `hre : ∀ n : ℕ, (zetaMul χ n * (t : ℂ) ^ n).re = (zetaMul χ n).re * t ^ n`. Introduce `n`. Rewrite using `[← Complex.ofReal_pow, Complex.re_mul_ofReal]`. Simplify using `only [hre] at h3`.

Set `g : ℕ → ℕ+` to `fun m => m.succPNat ^ 2`. Establish `hg : Function.Injective g`. Introduce `a b hab`. Use `congrArg PNat.val hab` as an intermediate fact. Simplify using `only [g, PNat.pow_coe, Nat.succPNat_coe] at this`.

Use `Nat.pow_left_injective two_ne_zero this` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `le_trans ?_ (sum_le_hasSum ((Finset.range M).image g) (fun n _ => ?_) h3)` and prove the remaining obligations. Rewrite using `[Finset.sum_image fun a _ b _ h => hg h]`. Establish `: ∀ m ∈ Finset.range M, (1 / 3 : ℝ) ≤ (zetaMul χ (g m)).re * t ^ (g m : ℕ)`.

Introduce `m hm`. Establish `hgm : (g m : ℕ) = (m + 1) ^ 2` using `by simp [g]`. Rewrite using `[hgm]`. Establish `h4 : 1 ≤ (zetaMul χ ((m + 1) ^ 2)).re` using `(Complex.le_def.1 (one_le_zetaMul_sq hχ (Nat.succ_ne_zero m))).1`. Establish `h5 : t ^ (M ^ 2) ≤ t ^ ((m + 1) ^ 2)` using `pow_le_pow_of_le_one ht0.le ht1.le (Nat.pow_le_pow_left (Finset.mem_range.1 hm) 2)`.

Establish `h6 : t ^ (M ^ 2) = Real.exp (-1)`. Rewrite using `[ht, ← Real.exp_nat_mul, hα]`. Use `congr 1`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Establish `h7 : (1 / 3 : ℝ) ≤ Real.exp (-1)` using `by linarith [Real.exp_neg_one_gt_d9]`. Use the polynomial consequences of the given equalities and inequalities. Use `Finset.card_nsmul_le_sum _ _ _ this` as an intermediate fact. Simplify `this` using `[div_eq_mul_inv]`. Conclude with `mul_nonneg (Complex.le_def.1 (zetaMul_nonneg hχ n)).1 (pow_nonneg ht0.le _)`.
-/
theorem lambert_lower {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) {M : ℕ}
    (hM : 0 < M) :
    (M : ℝ) / 3 ≤ ‖∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((Real.exp (((d + 1 : ℕ) : ℝ) * ((M : ℝ) ^ 2)⁻¹) - 1)⁻¹ : ℝ) : ℂ)‖ := by
  set α : ℝ := ((M : ℝ) ^ 2)⁻¹ with hα
  have hα0 : 0 < α := by positivity
  set t : ℝ := Real.exp (-α) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hn : ‖(t : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg ht0.le]
  have h1 := lambert χ hn
  rw [tsum_pnat_eq_tsum_succ
    (f := fun d : ℕ => χ (d : ZMod q) * ((t : ℂ) ^ d / (1 - (t : ℂ) ^ d)))] at h1
  have e : ∀ d : ℕ, (((Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ) : ℂ)
      = (t : ℂ) ^ (d + 1) / (1 - (t : ℂ) ^ (d + 1)) := by
    intro d
    have : t ^ (d + 1) = (Real.exp (((d + 1 : ℕ) : ℝ) * α))⁻¹ := by
      rw [ht, ← Real.exp_nat_mul, ← Real.exp_neg, mul_neg]
    have h2 : (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ = t ^ (d + 1) / (1 - t ^ (d + 1)) := by
      rw [this]
      have h3 : 0 < ((d + 1 : ℕ) : ℝ) * α := by positivity
      have h4 := Real.add_one_le_exp (((d + 1 : ℕ) : ℝ) * α)
      generalize Real.exp (((d + 1 : ℕ) : ℝ) * α) = E at *
      have h5 : E - 1 ≠ 0 := by linarith
      have h6 : E ≠ 0 := by linarith
      field_simp
    rw [h2]
    push_cast
    rfl
  simp only [e]
  refine le_trans ?_ (Complex.re_le_norm _)
  have h3 := Complex.hasSum_re h1
  have hre : ∀ n : ℕ, (zetaMul χ n * (t : ℂ) ^ n).re = (zetaMul χ n).re * t ^ n := by
    intro n
    rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
  simp only [hre] at h3
  let g : ℕ → ℕ+ := fun m => m.succPNat ^ 2
  have hg : Function.Injective g := by
    intro a b hab
    have := congrArg PNat.val hab
    simp only [g, PNat.pow_coe, Nat.succPNat_coe] at this
    have := Nat.pow_left_injective two_ne_zero this
    omega
  refine le_trans ?_ (sum_le_hasSum ((Finset.range M).image g) (fun n _ => ?_) h3)
  · rw [Finset.sum_image fun a _ b _ h => hg h]
    have : ∀ m ∈ Finset.range M, (1 / 3 : ℝ) ≤ (zetaMul χ (g m)).re * t ^ (g m : ℕ) := by
      intro m hm
      have hgm : (g m : ℕ) = (m + 1) ^ 2 := by simp [g]
      rw [hgm]
      have h4 : 1 ≤ (zetaMul χ ((m + 1) ^ 2)).re :=
        (Complex.le_def.1 (one_le_zetaMul_sq hχ (Nat.succ_ne_zero m))).1
      have h5 : t ^ (M ^ 2) ≤ t ^ ((m + 1) ^ 2) :=
        pow_le_pow_of_le_one ht0.le ht1.le
          (Nat.pow_le_pow_left (Finset.mem_range.1 hm) 2)
      have h6 : t ^ (M ^ 2) = Real.exp (-1) := by
        rw [ht, ← Real.exp_nat_mul, hα]
        congr 1
        push_cast
        field_simp
      have h7 : (1 / 3 : ℝ) ≤ Real.exp (-1) := by linarith [Real.exp_neg_one_gt_d9]
      nlinarith
    have := Finset.card_nsmul_le_sum _ _ _ this
    simpa [div_eq_mul_inv] using this
  · exact mul_nonneg (Complex.le_def.1 (zetaMul_nonneg hχ n)).1 (pow_nonneg ht0.le _)

/- English proof (translation)
Establish `h : Summable fun d : ℕ => (2 * (α ^ 2)⁻¹) * (((d + 1 : ℕ) : ℝ) ^ 2)⁻¹` using `((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)).mul_left _`. Use `Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) h` and prove the remaining obligations. Establish `h3 : 0 < ((d + 1 : ℕ) : ℝ) * α` using `by positivity`. Establish `h4` using `Real.add_one_le_exp (((d + 1 : ℕ) : ℝ) * α)`. Conclude with `inv_nonneg.2 (by linarith)`.

Establish `h3 : 0 < ((d + 1 : ℕ) : ℝ) * α` using `by positivity`. Establish `h4` using `Real.quadratic_le_exp_of_nonneg h3.le`. Establish `: 2 * (α ^ 2)⁻¹ * (((d + 1 : ℕ) : ℝ) ^ 2)⁻¹ = ((((d + 1 : ℕ) : ℝ) * α) ^ 2 / 2)⁻¹`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this]`.

Conclude with `inv_anti₀ (by positivity) (by linarith)`.
-/
theorem summable_inv_exp {α : ℝ} (hα : 0 < α) :
    Summable fun d : ℕ => (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ := by
  have h : Summable fun d : ℕ => (2 * (α ^ 2)⁻¹) * (((d + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
    ((summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) 1).2
      (Real.summable_nat_pow_inv.2 one_lt_two)).mul_left _
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) h
  · have h3 : 0 < ((d + 1 : ℕ) : ℝ) * α := by positivity
    have h4 := Real.add_one_le_exp (((d + 1 : ℕ) : ℝ) * α)
    exact inv_nonneg.2 (by linarith)
  · have h3 : 0 < ((d + 1 : ℕ) : ℝ) * α := by positivity
    have h4 := Real.quadratic_le_exp_of_nonneg h3.le
    have : 2 * (α ^ 2)⁻¹ * (((d + 1 : ℕ) : ℝ) ^ 2)⁻¹ = ((((d + 1 : ℕ) : ℝ) * α) ^ 2 / 2)⁻¹ := by
      field_simp
    rw [this]
    exact inv_anti₀ (by positivity) (by linarith)

/- English proof (translation)
Establish `hs : 1 < (1 + (ε : ℂ)).re` using `by simpa using hε`. Establish `h1 : LSeriesHasSum (χ ·) (1 + ε) (LFunction χ (1 + ε))`. Rewrite using `[LFunction_eq_LSeries χ hs]`. Conclude with `(LSeriesSummable_of_one_lt_re χ hs).LSeriesHasSum`. Establish `h2` using `((hasSum_nat_add_iff' 1).2 h1).mul_right ((α⁻¹ : ℝ) : ℂ)`.

Simplify using `only [Finset.range_one, Finset.sum_singleton, LSeries.term_zero, sub_zero] at h2`. Establish `hp : ∀ d : ℕ, ((d + 1 : ℕ) : ℝ) ^ (-ε) ≤ 1` using `fun d => Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)`. Establish `h3 : Summable fun d : ℕ => χ ((d + 1 : ℕ) : ZMod q) * (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ)`. Use `Summable.of_norm_bounded (summable_inv_exp hα).norm fun d => ?_` and prove the remaining obligations. Rewrite using `[norm_mul, Complex.norm_real, norm_mul]`.

Use `(mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans ?_` and prove the remaining obligations. Use `mul_le_of_le_one_left (by positivity) ?_` and prove the remaining obligations. Rewrite using `[Real.norm_of_nonneg (by positivity)]`. Conclude with `hp d`. Establish `h4` using `h2.sub h3.hasSum`.

Set `b : ℕ → ℝ` to `fun d => ((d + 1 : ℕ) : ℝ) ^ (-ε) * wt (((d + 1 : ℕ) : ℝ) * α)`. Establish `h5 : ∀ d : ℕ, LSeries.term (χ ·) (1 + ε) (d + 1) * ((α⁻¹ : ℝ) : ℂ) - χ ((d + 1 : ℕ) : ZMod q) * (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ) = χ ((d + 1 : ℕ) : ZMod q) * (b d : ℂ)`. Introduce `d`. Rewrite using `[LSeries.term_of_ne_zero (Nat.succ_ne_zero d)]`. Establish `: ((d + 1 : ℕ) : ℂ) ^ (1 + (ε : ℂ)) = ((((d + 1 : ℕ) : ℝ) ^ (1 + ε) : ℝ) : ℂ)`.

Rewrite using `[Complex.ofReal_cpow (by positivity)]`. Simplify using the standard rewrite rules. Rewrite using `[this, div_eq_mul_inv, mul_assoc, ← mul_sub, ← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_sub]`. Use `congr 2`. Simplify using `only [b, wt]`.

Rewrite using `[Real.rpow_add (by positivity), Real.rpow_one, Real.rpow_neg (by positivity)]`. Simplify using `only [mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [h5] at h4`. Establish `hw : ∀ d : ℕ, 0 < ((d + 1 : ℕ) : ℝ) * α` using `fun d => by positivity`.

Establish `hb0 : ∀ d, 0 ≤ b d` using `fun d => mul_nonneg (by positivity) (wt_nonneg (hw d))`. Establish `hb : Antitone b`. Introduce `m n hmn`. Establish `hc : ((m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ)` using `by exact_mod_cast Nat.succ_le_succ hmn`. Use `mul_le_mul ?_ ?_ (wt_nonneg (hw n)) (by positivity)` and prove the remaining obligations.

Conclude with `Real.rpow_le_rpow_of_nonpos (by positivity) hc (by linarith)`. Conclude with `wt_antitoneOn (hw m) (hw n) (by gcongr)`. Establish `hb1 : b 0 ≤ 1` using `mul_le_one₀ (hp 0) (wt_nonneg (hw 0)) (wt_le_one (hw 0))`. Use `le_of_tendsto' h4.tendsto_sum_nat.norm fun N => ?_` and prove the remaining obligations. Use `(abel_bound _ b q (char_sum_bound χ hχ) hb hb0 N).trans ?_` and prove the remaining obligations.

Conclude with `mul_le_of_le_one_right (by positivity) hb1`.
-/
theorem compare_right {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {α ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε) :
    ‖LFunction χ (1 + ε) * ((α⁻¹ : ℝ) : ℂ) - ∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ)‖ ≤ q := by
  have hs : 1 < (1 + (ε : ℂ)).re := by simpa using hε
  have h1 : LSeriesHasSum (χ ·) (1 + ε) (LFunction χ (1 + ε)) := by
    rw [LFunction_eq_LSeries χ hs]
    exact (LSeriesSummable_of_one_lt_re χ hs).LSeriesHasSum
  have h2 := ((hasSum_nat_add_iff' 1).2 h1).mul_right ((α⁻¹ : ℝ) : ℂ)
  simp only [Finset.range_one, Finset.sum_singleton, LSeries.term_zero, sub_zero] at h2
  have hp : ∀ d : ℕ, ((d + 1 : ℕ) : ℝ) ^ (-ε) ≤ 1 := fun d =>
    Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)
  have h3 : Summable fun d : ℕ => χ ((d + 1 : ℕ) : ZMod q) *
      (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ) := by
    refine Summable.of_norm_bounded (summable_inv_exp hα).norm fun d => ?_
    rw [norm_mul, Complex.norm_real, norm_mul]
    refine (mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans ?_
    refine mul_le_of_le_one_left (by positivity) ?_
    rw [Real.norm_of_nonneg (by positivity)]
    exact hp d
  have h4 := h2.sub h3.hasSum
  let b : ℕ → ℝ := fun d => ((d + 1 : ℕ) : ℝ) ^ (-ε) * wt (((d + 1 : ℕ) : ℝ) * α)
  have h5 : ∀ d : ℕ, LSeries.term (χ ·) (1 + ε) (d + 1) * ((α⁻¹ : ℝ) : ℂ)
      - χ ((d + 1 : ℕ) : ZMod q) *
      (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ)
      = χ ((d + 1 : ℕ) : ZMod q) * (b d : ℂ) := by
    intro d
    rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero d)]
    have : ((d + 1 : ℕ) : ℂ) ^ (1 + (ε : ℂ)) = ((((d + 1 : ℕ) : ℝ) ^ (1 + ε) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by positivity)]
      simp
    rw [this, div_eq_mul_inv, mul_assoc, ← mul_sub, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub]
    congr 2
    simp only [b, wt]
    rw [Real.rpow_add (by positivity), Real.rpow_one, Real.rpow_neg (by positivity)]
    simp only [mul_inv]
    ring
  simp only [h5] at h4
  have hw : ∀ d : ℕ, 0 < ((d + 1 : ℕ) : ℝ) * α := fun d => by positivity
  have hb0 : ∀ d, 0 ≤ b d := fun d => mul_nonneg (by positivity) (wt_nonneg (hw d))
  have hb : Antitone b := by
    intro m n hmn
    have hc : ((m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hmn
    refine mul_le_mul ?_ ?_ (wt_nonneg (hw n)) (by positivity)
    · exact Real.rpow_le_rpow_of_nonpos (by positivity) hc (by linarith)
    · exact wt_antitoneOn (hw m) (hw n) (by gcongr)
  have hb1 : b 0 ≤ 1 := mul_le_one₀ (hp 0) (wt_nonneg (hw 0)) (wt_le_one (hw 0))
  refine le_of_tendsto' h4.tendsto_sum_nat.norm fun N => ?_
  refine (abel_bound _ b q (char_sum_bound χ hχ) hb hb0 N).trans ?_
  exact mul_le_of_le_one_right (by positivity) hb1

/- English proof (translation)
Establish `h1 : Tendsto (fun ε : ℝ => LFunction χ (1 + ε)) (𝓝[>] 0) (𝓝 (LFunction χ 1))`. Establish `: Continuous fun ε : ℝ => LFunction χ (1 + ε)` using `(differentiable_LFunction hχ).continuous.comp (by fun_prop)`. Simplify using `using (this.tendsto 0).mono_left nhdsWithin_le_nhds`. Establish `h2 : Tendsto (fun ε : ℝ => ∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) * (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ)) (𝓝[>] 0) (𝓝 (∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) * (((Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ) : ℂ)))`. Use `tendsto_tsum_of_dominated_convergence (summable_inv_exp hα).norm (fun d => ?_) ?_` and prove the remaining obligations.

Establish `hc : Continuous fun ε : ℝ => ((d + 1 : ℕ) : ℝ) ^ (-ε)` using `(Real.continuous_const_rpow (by positivity)).comp continuous_neg`. Establish `: Continuous fun ε : ℝ => χ ((d + 1 : ℕ) : ZMod q) * (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ)` using `continuous_const.mul (Complex.continuous_ofReal.comp (hc.mul continuous_const))`. Use `(this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))` as an intermediate fact. Rewrite `this` using `[neg_zero, Real.rpow_zero, one_mul]`. Then use the resulting hypothesis. Use `filter_upwards [self_mem_nhdsWithin] with ε hε d`.

Establish `hε' : 0 < ε` using `hε`. Rewrite using `[norm_mul, Complex.norm_real, norm_mul]`. Use `(mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans ?_` and prove the remaining obligations. Use `mul_le_of_le_one_left (by positivity) ?_` and prove the remaining obligations. Rewrite using `[Real.norm_of_nonneg (by positivity)]`.

Conclude with `Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)`. Use `le_of_tendsto ((h1.mul_const _).sub h2).norm ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with ε hε`. Conclude with `compare_right χ hχ hα hε`.
-/
theorem compare_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) {α : ℝ}
    (hα : 0 < α) :
    ‖LFunction χ 1 * ((α⁻¹ : ℝ) : ℂ) - ∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ) : ℂ)‖ ≤ q := by
  have h1 : Tendsto (fun ε : ℝ => LFunction χ (1 + ε)) (𝓝[>] 0) (𝓝 (LFunction χ 1)) := by
    have : Continuous fun ε : ℝ => LFunction χ (1 + ε) :=
      (differentiable_LFunction hχ).continuous.comp (by fun_prop)
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun ε : ℝ => ∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ))
      (𝓝[>] 0) (𝓝 (∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ) : ℂ))) := by
    refine tendsto_tsum_of_dominated_convergence (summable_inv_exp hα).norm (fun d => ?_) ?_
    · have hc : Continuous fun ε : ℝ => ((d + 1 : ℕ) : ℝ) ^ (-ε) :=
        (Real.continuous_const_rpow (by positivity)).comp continuous_neg
      have : Continuous fun ε : ℝ => χ ((d + 1 : ℕ) : ZMod q) *
        (((((d + 1 : ℕ) : ℝ) ^ (-ε) * (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ)) : ℂ) :=
        continuous_const.mul (Complex.continuous_ofReal.comp (hc.mul continuous_const))
      have := (this.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      rwa [neg_zero, Real.rpow_zero, one_mul] at this
    · filter_upwards [self_mem_nhdsWithin] with ε hε d
      have hε' : 0 < ε := hε
      rw [norm_mul, Complex.norm_real, norm_mul]
      refine (mul_le_of_le_one_left (by positivity) (χ.norm_le_one _)).trans ?_
      refine mul_le_of_le_one_left (by positivity) ?_
      rw [Real.norm_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by simp) (by linarith)
  refine le_of_tendsto ((h1.mul_const _).sub h2).norm ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact compare_right χ hχ hα hε

/- English proof (translation)
Establish `hq : 0 < q` using `NeZero.pos q`. Establish `hq' : (0 : ℝ) < q` using `by exact_mod_cast hq`. Establish `h1` using `lambert_lower h2 (M := 6 * q) (by omega)`. Establish `h3` using `compare_one χ hχ (α := (((6 * q : ℕ) : ℝ) ^ 2)⁻¹) (by positivity)`. Rewrite `h3` using `[norm_sub_rev]`.

Establish `h4` using `(norm_sub_norm_le _ _).trans h3`. Rewrite `h4` using `[norm_mul, Complex.norm_real, inv_inv, Real.norm_of_nonneg (by positivity)]`. Establish `h5` using `(sub_le_sub_right h1 _).trans h4`. Move the coercions through the operations in `at h5`. Rewrite using `[div_le_iff₀ (by positivity)]`.

Use `le_of_mul_le_mul_right ?_ hq'` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem inv_le_norm_LFunction_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (h2 : χ ^ 2 = 1) : 1 / (36 * (q : ℝ)) ≤ ‖LFunction χ 1‖ := by
  have hq : 0 < q := NeZero.pos q
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h1 := lambert_lower h2 (M := 6 * q) (by omega)
  have h3 := compare_one χ hχ (α := (((6 * q : ℕ) : ℝ) ^ 2)⁻¹) (by positivity)
  rw [norm_sub_rev] at h3
  have h4 := (norm_sub_norm_le _ _).trans h3
  rw [norm_mul, Complex.norm_real, inv_inv, Real.norm_of_nonneg (by positivity)] at h4
  have h5 := (sub_le_sub_right h1 _).trans h4
  push_cast at h5
  rw [div_le_iff₀ (by positivity)]
  refine le_of_mul_le_mul_right ?_ hq'
  nlinarith

/- English proof (translation)
Use `⟨1 / 36, by norm_num, fun q _ χ h1 h2 => le_trans ?_ (inv_le_norm_LFunction_one χ h1 h2)⟩` and prove the remaining obligations. Establish `hq : (1 : ℝ) ≤ q` using `by exact_mod_cast NeZero.pos q`. Establish `: (q : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 2)` using `Real.self_le_rpow_of_one_le hq (by norm_num)`. Rewrite using `[div_div]`. Use `gcongr`.
-/
theorem exists_le_norm_LFunction_one : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ ≠ 1 → χ ^ 2 = 1 →
      c / (q : ℝ) ^ ((3 : ℝ) / 2) ≤ ‖LFunction χ 1‖ := by
  refine ⟨1 / 36, by norm_num, fun q _ χ h1 h2 => le_trans ?_ (inv_le_norm_LFunction_one χ h1 h2)⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have : (q : ℝ) ≤ (q : ℝ) ^ ((3 : ℝ) / 2) := Real.self_le_rpow_of_one_le hq (by norm_num)
  rw [div_div]
  gcongr

end GlobalTheory.LOneLower
