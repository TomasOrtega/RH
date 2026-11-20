import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq

noncomputable section

open Finset Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

/- English proof (translation)
Use `continuous_matrix fun a b => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : b < a ∧ ε a ≠ ε b`. Simplify using `only [pmat, dif_pos h1]`. Conclude with `continuous_apply _`. Distinguish the cases in `h2 : a < b ∧ ε b ≠ ε a`.

Simplify using `only [pmat, dif_neg h1, dif_pos h2]`. Conclude with `(continuous_apply _).star`. Simplify using `only [pmat, dif_neg h1, dif_neg h2]`. Conclude with `continuous_const`.
-/
theorem pmat_continuous (ε : Fin n → Bool) : Continuous (fun z : PCoord ε → ℂ => pmat z) := by
  refine continuous_matrix fun a b => ?_
  by_cases h1 : b < a ∧ ε a ≠ ε b
  · simp only [pmat, dif_pos h1]; exact continuous_apply _
  · by_cases h2 : a < b ∧ ε b ≠ ε a
    · simp only [pmat, dif_neg h1, dif_pos h2]; exact (continuous_apply _).star
    · simp only [pmat, dif_neg h1, dif_neg h2]; exact continuous_const

/- English proof (translation)
Use `conv_lhs => rw [hA.spectral_theorem, ← map_pow]`. Use `first`. Consider the case `(rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow, Matrix.trace_diagonal] simp)`. Consider the case `simp [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Matrix.diagonal_pow, Matrix.trace_diagonal]`.
-/
theorem pb_trace_pow_herm {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (j : ℕ) :
    (A ^ j).trace = ∑ a, ((hA.eigenvalues a : ℝ) : ℂ) ^ j := by
  conv_lhs => rw [hA.spectral_theorem, ← map_pow]
  first
    | (rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul,
        Matrix.diagonal_pow, Matrix.trace_diagonal]
       simp)
    | simp [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle, Matrix.diagonal_pow, Matrix.trace_diagonal]

/- English proof (translation)
Establish `h : (fun z : PCoord ε → ℂ => ∑ a, pev z a ^ j) = fun z => ((pmat z) ^ j).trace.re`. Use function extensionality and compare the values at `z`. Rewrite using `[pb_trace_pow_herm (pmat_isHermitian z) j, Complex.re_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => by`. Rewrite using `[← Complex.ofReal_pow, Complex.ofReal_re]`.

Apply the tactic sequence `try rfl`. Rewrite using `[h]`. Conclude with `Complex.continuous_re.comp (((pmat_continuous ε).pow j).matrix_trace)`.
-/
theorem psum_continuous (ε : Fin n → Bool) (j : ℕ) :
    Continuous (fun z : PCoord ε → ℂ => ∑ a, pev z a ^ j) := by
  have h : (fun z : PCoord ε → ℂ => ∑ a, pev z a ^ j) = fun z => ((pmat z) ^ j).trace.re := by
    funext z
    rw [pb_trace_pow_herm (pmat_isHermitian z) j, Complex.re_sum]
    exact Finset.sum_congr rfl fun a _ => by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
      try rfl
  rw [h]
  exact Complex.continuous_re.comp (((pmat_continuous ε).pow j).matrix_trace)

/- English proof (translation)
Establish `h : (fun z : PCoord ε → ℂ => ∑ b, (-pev z b) ^ j) = fun z => (-1) ^ j * ∑ b, pev z b ^ j`. Use function extensionality and compare the values at `z`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun b _ => neg_pow _ _`. Rewrite using `[h]`.

Conclude with `continuous_const.mul (psum_continuous ε j)`.
-/
theorem negpsum_continuous (ε : Fin n → Bool) (j : ℕ) :
    Continuous (fun z : PCoord ε → ℂ => ∑ b, (-pev z b) ^ j) := by
  have h : (fun z : PCoord ε → ℂ => ∑ b, (-pev z b) ^ j) = fun z => (-1) ^ j * ∑ b, pev z b ^ j := by
    funext z
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => neg_pow _ _
  rw [h]
  exact continuous_const.mul (psum_continuous ε j)

/- English proof (translation)
Establish `h : (fun z : PCoord ε → ℂ => ∑ a, ∑ b, (pev z a - pev z b) ^ k) = fun z => ∑ i ∈ range (k + 1), (∑ a, pev z a ^ i) * (∑ b, (-pev z b) ^ (k - i)) * (k.choose i : ℝ)`. Use function extensionality and compare the values at `z`. Repeatedly rewrite using `[sub_eq_add_neg, add_pow, Finset.sum_mul_sum, Finset.sum_mul]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `arg 2`.

Use extensionality with `a`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[h]`. Conclude with `continuous_finset_sum _ fun i _ => ((psum_continuous ε i).mul (negpsum_continuous ε (k - i))).mul continuous_const`.
-/
theorem pairpow_continuous (ε : Fin n → Bool) (k : ℕ) :
    Continuous (fun z : PCoord ε → ℂ => ∑ a, ∑ b, (pev z a - pev z b) ^ k) := by
  have h : (fun z : PCoord ε → ℂ => ∑ a, ∑ b, (pev z a - pev z b) ^ k) =
      fun z => ∑ i ∈ range (k + 1),
        (∑ a, pev z a ^ i) * (∑ b, (-pev z b) ^ (k - i)) * (k.choose i : ℝ) := by
    funext z
    simp_rw [sub_eq_add_neg, add_pow, Finset.sum_mul_sum, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]; arg 2; ext a; rw [Finset.sum_comm]
  rw [h]
  exact continuous_finset_sum _ fun i _ =>
    ((psum_continuous ε i).mul (negpsum_continuous ε (k - i))).mul continuous_const

/- English proof (translation)
Establish `h : (fun z : PCoord ε → ℂ => ∑ a, ∑ b, P.eval (pev z a - pev z b)) = fun z => ∑ i ∈ range (P.natDegree + 1), P.coeff i * ∑ a, ∑ b, (pev z a - pev z b) ^ i`. Use function extensionality and compare the values at `z`. Repeatedly rewrite using `[Polynomial.eval_eq_sum_range, Finset.mul_sum]`. Use `conv_rhs => rw [Finset.sum_comm]`. Use `arg 2`.

Use extensionality with `a`. Rewrite using `[Finset.sum_comm]`. Rewrite using `[h]`. Conclude with `continuous_finset_sum _ fun i _ => continuous_const.mul (pairpow_continuous ε i)`.
-/
theorem pairpoly_continuous (ε : Fin n → Bool) (P : Polynomial ℝ) :
    Continuous (fun z : PCoord ε → ℂ => ∑ a, ∑ b, P.eval (pev z a - pev z b)) := by
  have h : (fun z : PCoord ε → ℂ => ∑ a, ∑ b, P.eval (pev z a - pev z b)) =
      fun z => ∑ i ∈ range (P.natDegree + 1), P.coeff i * ∑ a, ∑ b, (pev z a - pev z b) ^ i := by
    funext z
    simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]; arg 2; ext a; rw [Finset.sum_comm]
  rw [h]
  exact continuous_finset_sum _ fun i _ => continuous_const.mul (pairpow_continuous ε i)

/- English proof (translation)
The claim follows from `|pev z a| ≤ Real.sqrt (∑ b, pev z b ^ 2) := by rw [← Real.sqrt_sq_eq_abs] exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun b => pev z b ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ a))`.
-/
theorem pb_abs_pev_le {ε : Fin n → Bool} (z : PCoord ε → ℂ) (a : Fin n) :
    |pev z a| ≤ Real.sqrt (∑ b, pev z b ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun b => pev z b ^ 2)
    (fun b _ => sq_nonneg _) (Finset.mem_univ a))

/- English proof (translation)
Establish `hS : Continuous (fun z : PCoord ε → ℂ => Real.sqrt (∑ b, pev z b ^ 2))` using `(psum_continuous ε 2).sqrt`. Rewrite using `[Metric.continuous_iff]`. Introduce `z0 e he`. Take `⟨δ1, hδ1, h1⟩` from `Metric.continuous_iff.1 hS z0 1 one_pos`. Take `⟨R, hR⟩ : ∃ R : ℝ, R = Real.sqrt (∑ b, pev z0 b ^ 2) + 1` from `⟨_, rfl⟩`.

Establish `hbd : ∀ z, dist z z0 < δ1 → ∀ a b, pev z a - pev z b ∈ Set.Icc (-(2 * R)) (2 * R)`. Introduce `z hz a b`. Establish `hSz : Real.sqrt (∑ b, pev z b ^ 2) ≤ R`. Establish `h1z` using `h1 z hz`. Rewrite `h1z` using `[Real.dist_eq]`.

Combine the linear relations using `[(abs_lt.1 h1z).2]`. Establish `ha` using `abs_le.1 ((pb_abs_pev_le z a).trans hSz)`. Establish `hb` using `abs_le.1 ((pb_abs_pev_le z b).trans hSz)`. Apply the tactic sequence `constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]`. Take `⟨η, hη⟩ : ∃ η : ℝ, η = e / (3 * ((n : ℝ) * n + 1))` from `⟨_, rfl⟩`.

Establish `hηpos : 0 < η` using `by rw [hη]; positivity`. Take `⟨p, hp⟩` from `exists_polynomial_near_of_continuousOn (-(2 * R)) (2 * R) h hc.continuousOn η hηpos`. Take `⟨δ2, hδ2, h2⟩` from `Metric.continuous_iff.1 (pairpoly_continuous ε p) z0 (e / 3) (by positivity)`. Use `⟨min δ1 δ2, lt_min hδ1 hδ2, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hz1 : dist z z0 < δ1` using `hz.trans_le (min_le_left _ _)`.

Establish `hz2 : dist z z0 < δ2` using `hz.trans_le (min_le_right _ _)`. Establish `happrox : ∀ w, dist w z0 < δ1 → |∑ a, ∑ b, h (pev w a - pev w b) - ∑ a, ∑ b, p.eval (pev w a - pev w b)| ≤ n * n * η`. Introduce `w hw`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans ?_` and prove the remaining obligations.

Establish `hrow : ∀ a, |∑ b, h (pev w a - pev w b) - ∑ b, p.eval (pev w a - pev w b)| ≤ n * η`. Introduce `a`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[abs_sub_comm]`. Conclude with `(hp _ (hbd w hw a b)).le`. Use `_ = n * η := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hA` using `abs_le.1 (happrox z hz1)`. Establish `hB` using `abs_le.1 (happrox z0 (by simpa using hδ1))`. Establish `hC` using `h2 z hz2`. Rewrite `hC` using `[Real.dist_eq]`.

Establish `hsmall : (n : ℝ) * n * η < e / 3`. Establish `hq : (n : ℝ) * n / (n * n + 1) < 1` using `(div_lt_one (by positivity)).2 (by linarith)`. Establish `heq : (n : ℝ) * n * η = e / 3 * ((n * n) / (n * n + 1))`. Rewrite using `[hη]`. Apply the tactic sequence `first | (field_simp; ring) | field_simp | ring`.

Rewrite using `[heq]`. Conclude with `mul_lt_of_lt_one_right (by positivity) hq`. Rewrite using `[Real.dist_eq]`. Establish `hC'` using `abs_lt.1 hC`. Conclude with `abs_sub_lt_iff.2 ⟨by linarith [hA.1, hA.2, hB.1, hB.2, hC'.1, hC'.2], by linarith [hA.1, hA.2, hB.1, hB.2, hC'.1, hC'.2]⟩`.
-/
theorem pairfun_continuous (ε : Fin n → Bool) (h : ℝ → ℝ) (hc : Continuous h) :
    Continuous (fun z : PCoord ε → ℂ => ∑ a, ∑ b, h (pev z a - pev z b)) := by
  have hS : Continuous (fun z : PCoord ε → ℂ => Real.sqrt (∑ b, pev z b ^ 2)) :=
    (psum_continuous ε 2).sqrt
  rw [Metric.continuous_iff]
  intro z0 e he
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuous_iff.1 hS z0 1 one_pos
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = Real.sqrt (∑ b, pev z0 b ^ 2) + 1 := ⟨_, rfl⟩
  have hbd : ∀ z, dist z z0 < δ1 → ∀ a b, pev z a - pev z b ∈ Set.Icc (-(2 * R)) (2 * R) := by
    intro z hz a b
    have hSz : Real.sqrt (∑ b, pev z b ^ 2) ≤ R := by
      have h1z := h1 z hz
      rw [Real.dist_eq] at h1z
      linarith [(abs_lt.1 h1z).2]
    have ha := abs_le.1 ((pb_abs_pev_le z a).trans hSz)
    have hb := abs_le.1 ((pb_abs_pev_le z b).trans hSz)
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = e / (3 * ((n : ℝ) * n + 1)) := ⟨_, rfl⟩
  have hηpos : 0 < η := by rw [hη]; positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-(2 * R)) (2 * R) h hc.continuousOn η hηpos
  obtain ⟨δ2, hδ2, h2⟩ := Metric.continuous_iff.1 (pairpoly_continuous ε p) z0 (e / 3) (by positivity)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun z hz => ?_⟩
  have hz1 : dist z z0 < δ1 := hz.trans_le (min_le_left _ _)
  have hz2 : dist z z0 < δ2 := hz.trans_le (min_le_right _ _)
  have happrox : ∀ w, dist w z0 < δ1 →
      |∑ a, ∑ b, h (pev w a - pev w b) - ∑ a, ∑ b, p.eval (pev w a - pev w b)| ≤ n * n * η := by
    intro w hw
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hrow : ∀ a, |∑ b, h (pev w a - pev w b) - ∑ b, p.eval (pev w a - pev w b)| ≤ n * η := by
      intro a
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ b, |h (pev w a - pev w b) - p.eval (pev w a - pev w b)| ≤ ∑ _b : Fin n, η :=
            Finset.sum_le_sum fun b _ => by
              rw [abs_sub_comm]; exact (hp _ (hbd w hw a b)).le
        _ = n * η := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ∑ a, |∑ b, h (pev w a - pev w b) - ∑ b, p.eval (pev w a - pev w b)| ≤ ∑ _a : Fin n, (n * η) :=
          Finset.sum_le_sum fun a _ => hrow a
      _ = n * n * η := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hA := abs_le.1 (happrox z hz1)
  have hB := abs_le.1 (happrox z0 (by simpa using hδ1))
  have hC := h2 z hz2
  rw [Real.dist_eq] at hC
  have hsmall : (n : ℝ) * n * η < e / 3 := by
    have hq : (n : ℝ) * n / (n * n + 1) < 1 := (div_lt_one (by positivity)).2 (by linarith)
    have heq : (n : ℝ) * n * η = e / 3 * ((n * n) / (n * n + 1)) := by
      rw [hη]
      first | (field_simp; ring) | field_simp | ring
    rw [heq]
    exact mul_lt_of_lt_one_right (by positivity) hq
  rw [Real.dist_eq]
  have hC' := abs_lt.1 hC
  exact abs_sub_lt_iff.2 ⟨by linarith [hA.1, hA.2, hB.1, hB.2, hC'.1, hC'.2],
    by linarith [hA.1, hA.2, hB.1, hB.2, hC'.1, hC'.2]⟩

/- English proof (translation)
Use function extensionality and compare the values at `u`. Rewrite using `[Function.update_apply]`. Both sides reduce to the same expression.
-/
theorem pb_shc_eq_update : shc = Function.update (fun u : ℝ => Real.sinh u / u) 0 1 := by
  funext u
  rw [Function.update_apply]
  rfl

/- English proof (translation)
Rewrite using `[pb_shc_eq_update, continuous_iff_continuousAt]`. Introduce `u`. Distinguish the cases in `hu : u = 0`. Substitute `hu` using the available equality. Rewrite using `[continuousAt_update_same]`.

Establish `hd` using `Real.hasDerivAt_sinh 0`. Rewrite `hd` using `[hasDerivAt_iff_tendsto_slope, Real.cosh_zero]`. Use `hd.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with v hv`. Rewrite using `[slope_def_field]`.

Simplify using the standard rewrite rules. Rewrite using `[continuousAt_update_of_ne hu]`. Conclude with `(Real.continuous_sinh.continuousAt).div continuousAt_id hu`.
-/
theorem pb_shc_continuous : Continuous shc := by
  rw [pb_shc_eq_update, continuous_iff_continuousAt]
  intro u
  by_cases hu : u = 0
  · subst hu
    rw [continuousAt_update_same]
    have hd := Real.hasDerivAt_sinh 0
    rw [hasDerivAt_iff_tendsto_slope, Real.cosh_zero] at hd
    refine hd.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v hv
    rw [slope_def_field]
    simp
  · rw [continuousAt_update_of_ne hu]
    exact (Real.continuous_sinh.continuousAt).div continuousAt_id hu

/- English proof (translation)
Unfold `shc`. Use `split_ifs with hu`. Conclude with `one_pos`. Break down `lt_or_gt_of_ne hu with h | h` into its components or cases. Conclude with `div_pos_of_neg_of_neg (Real.sinh_neg_iff.2 h) h`.

Conclude with `div_pos (Real.sinh_pos_iff.2 h) h`.
-/
theorem pb_shc_pos (u : ℝ) : 0 < shc u := by
  unfold shc
  split_ifs with hu
  · exact one_pos
  · rcases lt_or_gt_of_ne hu with h | h
    · exact div_pos_of_neg_of_neg (Real.sinh_neg_iff.2 h) h
    · exact div_pos (Real.sinh_pos_iff.2 h) h

/- English proof (translation)
Distinguish the cases in `hu : u = 0`. Simplify using `[shc, hu]`. Simplify using `[shc, hu, Real.sinh_neg, neg_div_neg_eq]`.
-/
theorem pb_shc_neg (u : ℝ) : shc (-u) = shc u := by
  by_cases hu : u = 0
  · simp [shc, hu]
  · simp [shc, hu, Real.sinh_neg, neg_div_neg_eq]

/- English proof (translation)
Establish `hpt : ∀ a b, f a b = (if a < b then f a b else 0) + (if b < a then f a b else 0)`. Introduce `a b`. Break down `lt_trichotomy a b with h | rfl | h` into its components or cases. Simplify using `[h, not_lt.2 h.le]`. Simplify using `[hd]`.

Simplify using `[h, not_lt.2 h.le]`. Establish `hswap : ∑ a, ∑ b, (if b < a then f a b else 0) = ∑ a, ∑ b, (if a < b then f a b else 0)`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hsym]`.

Establish `htot : ∑ a, ∑ b, f a b = 2 * ∑ a, ∑ b, (if a < b then f a b else 0)` using `by conv_lhs => enter [2, a, 2, b]; rw [hpt a b]`. Simplify using `only [Finset.sum_add_distrib]`. Rewrite using `[hswap]`. Expand and normalize the polynomial expressions, which then agree. Establish `hf : ∀ a, ∑ b ∈ univ.filter (fun b => a < b), f a b = ∑ b, (if a < b then f a b else 0)` using `fun a => Finset.sum_filter _ _`.

Repeatedly rewrite using `[hf]`. Rewrite using `[htot]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem pb_sum_pairs_half {f : Fin n → Fin n → ℝ} (hsym : ∀ a b, f a b = f b a) (hd : ∀ a, f a a = 0) :
    ∑ a, ∑ b ∈ univ.filter (fun b => a < b), f a b = (∑ a, ∑ b, f a b) / 2 := by
  have hpt : ∀ a b, f a b = (if a < b then f a b else 0) + (if b < a then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h, not_lt.2 h.le]
    · simp [hd]
    · simp [h, not_lt.2 h.le]
  have hswap : ∑ a, ∑ b, (if b < a then f a b else 0) = ∑ a, ∑ b, (if a < b then f a b else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsym]
  have htot : ∑ a, ∑ b, f a b = 2 * ∑ a, ∑ b, (if a < b then f a b else 0) := by
    conv_lhs => enter [2, a, 2, b]; rw [hpt a b]
    simp only [Finset.sum_add_distrib]
    rw [hswap]
    ring
  have hf : ∀ a, ∑ b ∈ univ.filter (fun b => a < b), f a b = ∑ b, (if a < b then f a b else 0) :=
    fun a => Finset.sum_filter _ _
  simp_rw [hf]
  rw [htot]
  ring

/- English proof (translation)
Establish `hsym : ∀ a b, Real.log (shc (pev z a - pev z b)) = Real.log (shc (pev z b - pev z a))`. Introduce `a b`. Rewrite using `[← neg_sub (pev z a) (pev z b), pb_shc_neg]`. Establish `hd : ∀ a, Real.log (shc (pev z a - pev z a)) = 0`. Introduce `a`.

Simplify using `[shc]`. Establish `hh` using `pb_sum_pairs_half (f := fun a b => Real.log (shc (pev z a - pev z b))) hsym hd`. Apply the tactic sequence `try simp only at hh`. Rewrite using `[← hh, Real.exp_sum]`. Unfold `Jac`.

Use `Finset.prod_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Real.exp_sum]`. Use `Finset.prod_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Real.exp_log (pb_shc_pos _)]`.
-/
theorem pb_jac_eq_exp {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    Jac z = Real.exp ((∑ a, ∑ b, Real.log (shc (pev z a - pev z b))) / 2) := by
  have hsym : ∀ a b, Real.log (shc (pev z a - pev z b)) = Real.log (shc (pev z b - pev z a)) := by
    intro a b
    rw [← neg_sub (pev z a) (pev z b), pb_shc_neg]
  have hd : ∀ a, Real.log (shc (pev z a - pev z a)) = 0 := by
    intro a
    simp [shc]
  have hh := pb_sum_pairs_half (f := fun a b => Real.log (shc (pev z a - pev z b))) hsym hd
  try simp only at hh
  rw [← hh, Real.exp_sum]
  unfold Jac
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Real.exp_sum]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Real.exp_log (pb_shc_pos _)]

/- English proof (translation)
Establish `h : (fun z : PCoord ε → ℂ => Jac z) = fun z => Real.exp ((∑ a, ∑ b, Real.log (shc (pev z a - pev z b))) / 2)` using `funext pb_jac_eq_exp`. Rewrite using `[h]`. Conclude with `Real.continuous_exp.comp ((pairfun_continuous ε _ (pb_shc_continuous.log fun u => (pb_shc_pos u).ne')).div_const 2)`.
-/
theorem pb_jac_continuous (ε : Fin n → Bool) : Continuous (fun z : PCoord ε → ℂ => Jac z) := by
  have h : (fun z : PCoord ε → ℂ => Jac z) =
      fun z => Real.exp ((∑ a, ∑ b, Real.log (shc (pev z a - pev z b))) / 2) := funext pb_jac_eq_exp
  rw [h]
  exact Real.continuous_exp.comp ((pairfun_continuous ε _
    (pb_shc_continuous.log fun u => (pb_shc_pos u).ne')).div_const 2)

end ReciprocityTheory.ChartRestriction.DS
