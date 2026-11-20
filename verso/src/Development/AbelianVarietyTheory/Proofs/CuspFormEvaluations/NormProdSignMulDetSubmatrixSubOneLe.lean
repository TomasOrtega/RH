import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantTheorems.ScaledBoundInequality
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ImportsAlt

open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram

namespace GlobalTheory

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.CuspFormEvaluationComplement.main`. Consider the case `exact _root_.GlobalTheory.CuspFormEvaluationComplement.main`. Consider the case `(apply _root_.GlobalTheory.CuspFormEvaluationComplement.main <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.CuspFormEvaluationComplement.main <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.CuspFormEvaluationComplement.main <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.CuspFormEvaluationComplement.main ..)`.
-/
theorem norm_multisetProd_sub_one_le_exp (s : Multiset ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hs : ∀ μ ∈ s, ‖μ - 1‖ ≤ t) : ‖s.prod - 1‖ ≤ Real.exp (s.card * t) - 1 := by
  first
  | exact @_root_.GlobalTheory.CuspFormEvaluationComplement.main
  | exact _root_.GlobalTheory.CuspFormEvaluationComplement.main
  | (apply _root_.GlobalTheory.CuspFormEvaluationComplement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CuspFormEvaluationComplement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CuspFormEvaluationComplement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CuspFormEvaluationComplement.main ..)

/- English proof (translation)
Establish `hs : ∀ μ ∈ (1 + M).charpoly.roots, ‖μ - 1‖ ≤ Fintype.card n * ε`. Introduce `μ hμ`. Establish `h1 : μ ∈ spectrum ℂ (1 + M)` using `mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots hμ)`. Establish `h2 : μ - 1 ∈ spectrum ℂ M`. Rewrite `h1`, the goal using `[spectrum.mem_iff]`.

Use `h1 using 2` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub, map_one]`. Normalize the expressions using the abelian group laws. Rewrite `h2` using `[← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]`. Take `⟨k, hk⟩` from `eigenvalue_mem_ball h2`.

Rewrite `hk` using `[Metric.mem_closedBall, dist_eq_norm]`. Establish `h3` using `Finset.add_sum_erase Finset.univ (fun j => ‖M k j‖) (Finset.mem_univ k)`. Establish `h4 : ∑ j, ‖M k j‖ ≤ Fintype.card n * ε`. Simplify using `using Finset.sum_le_card_nsmul Finset.univ (fun j => ‖M k j‖) ε fun j _ => hM k j`. Establish `h5` using `norm_le_insert' (μ - 1) (M k k)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc : (1 + M).charpoly.roots.card = Fintype.card n`. Rewrite using `[← charpoly_natDegree_eq_dim (1 + M)]`. Conclude with `(IsAlgClosed.splits _).natDegree_eq_card_roots.symm`. Establish `h` using `norm_multisetProd_sub_one_le_exp _ (by positivity) hs`.

Rewrite `h` using `[← det_eq_prod_roots_charpoly, hc]`. Then use the resulting hypothesis.
-/
theorem norm_det_one_add_sub_one_le_exp {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) {ε : ℝ} (hε : 0 ≤ ε) (hM : ∀ a b, ‖M a b‖ ≤ ε) :
    ‖(1 + M).det - 1‖ ≤ Real.exp (Fintype.card n * (Fintype.card n * ε)) - 1 := by
  have hs : ∀ μ ∈ (1 + M).charpoly.roots, ‖μ - 1‖ ≤ Fintype.card n * ε := by
    intro μ hμ
    have h1 : μ ∈ spectrum ℂ (1 + M) :=
      mem_spectrum_of_isRoot_charpoly (Polynomial.isRoot_of_mem_roots hμ)
    have h2 : μ - 1 ∈ spectrum ℂ M := by
      rw [spectrum.mem_iff] at h1 ⊢
      convert h1 using 2
      rw [map_sub, map_one]
      abel
    rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum] at h2
    obtain ⟨k, hk⟩ := eigenvalue_mem_ball h2
    rw [Metric.mem_closedBall, dist_eq_norm] at hk
    have h3 := Finset.add_sum_erase Finset.univ (fun j => ‖M k j‖) (Finset.mem_univ k)
    have h4 : ∑ j, ‖M k j‖ ≤ Fintype.card n * ε := by
      simpa using Finset.sum_le_card_nsmul Finset.univ (fun j => ‖M k j‖) ε fun j _ => hM k j
    have h5 := norm_le_insert' (μ - 1) (M k k)
    linarith
  have hc : (1 + M).charpoly.roots.card = Fintype.card n := by
    rw [← charpoly_natDegree_eq_dim (1 + M)]
    exact (IsAlgClosed.splits _).natDegree_eq_card_roots.symm
  have h := norm_multisetProd_sub_one_le_exp _ (by positivity) hs
  rwa [← det_eq_prod_roots_charpoly, hc] at h

/- English proof (translation)
Establish `hstar : (1 + z : Matrix (Fin r) (Fin r) ℂ).map star = 1 + z.map star`. Use extensionality with `a b`. Apply the tactic sequence `by_cases h : a = b <;> simp [one_apply, h]`. Establish `heq : (1 + z)ᵀ * diagonal j * (1 + z).map star - diagonal j = zᵀ * diagonal j + diagonal j * z.map star + zᵀ * diagonal j * z.map star`. Rewrite using `[hstar]`.

Simplify using `only [transpose_add, transpose_one]`. Use `noncomm_ring`. Rewrite using `[heq, Matrix.add_apply, Matrix.add_apply]`. Establish `h1 : ∀ a b, ‖(zᵀ * diagonal j) a b‖ ≤ δ` using `fun a b => by`. Rewrite using `[mul_diagonal, norm_mul, hj, mul_one]`.

Conclude with `hz _ _`. Establish `h2 : ‖(diagonal j * z.map star) a b‖ ≤ δ`. Rewrite using `[diagonal_mul, norm_mul, hj, one_mul, map_apply, norm_star]`. Conclude with `hz _ _`. Establish `h3 : ‖(zᵀ * diagonal j * z.map star) a b‖ ≤ r * (δ * δ)`.

Rewrite using `[mul_apply]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations. Use `Finset.sum_le_card_nsmul Finset.univ (fun k => ‖(zᵀ * diagonal j) a k * z.map star k b‖) (δ * δ) fun k _ => by` as an intermediate fact. Rewrite using `[norm_mul, map_apply, norm_star]`. Conclude with `mul_le_mul (h1 _ _) (hz _ _) (norm_nonneg _) hδ`.

Simplify using `using this`. Use `norm_add₃_le.trans ?_` and prove the remaining obligations. Use polynomial arithmetic with `[h1 a b]`.
-/
theorem norm_gram_sign_sub_le {r : ℕ} (j : Fin r → ℂ) (hj : ∀ a, ‖j a‖ = 1)
    (z : Matrix (Fin r) (Fin r) ℂ) {δ : ℝ} (hδ : 0 ≤ δ) (hr : r * δ ≤ 1) (hz : ∀ a b, ‖z a b‖ ≤ δ)
    (a b : Fin r) :
    ‖((1 + z)ᵀ * diagonal j * (1 + z).map star - diagonal j : Matrix (Fin r) (Fin r) ℂ) a b‖ ≤ 3 * δ := by
  have hstar : (1 + z : Matrix (Fin r) (Fin r) ℂ).map star = 1 + z.map star := by
    ext a b
    by_cases h : a = b <;> simp [one_apply, h]
  have heq : (1 + z)ᵀ * diagonal j * (1 + z).map star - diagonal j =
      zᵀ * diagonal j + diagonal j * z.map star + zᵀ * diagonal j * z.map star := by
    rw [hstar]
    simp only [transpose_add, transpose_one]
    noncomm_ring
  rw [heq, Matrix.add_apply, Matrix.add_apply]
  have h1 : ∀ a b, ‖(zᵀ * diagonal j) a b‖ ≤ δ := fun a b => by
    rw [mul_diagonal, norm_mul, hj, mul_one]; exact hz _ _
  have h2 : ‖(diagonal j * z.map star) a b‖ ≤ δ := by
    rw [diagonal_mul, norm_mul, hj, one_mul, map_apply, norm_star]; exact hz _ _
  have h3 : ‖(zᵀ * diagonal j * z.map star) a b‖ ≤ r * (δ * δ) := by
    rw [mul_apply]
    refine (norm_sum_le _ _).trans ?_
    have := Finset.sum_le_card_nsmul Finset.univ
      (fun k => ‖(zᵀ * diagonal j) a k * z.map star k b‖) (δ * δ) fun k _ => by
        rw [norm_mul, map_apply, norm_star]
        exact mul_le_mul (h1 _ _) (hz _ _) (norm_nonneg _) hδ
    simpa using this
  refine norm_add₃_le.trans ?_
  nlinarith [h1 a b]

/- English proof (translation)
Establish `hi : (i : ℝ) ≤ r`. Use `Fintype.card_le_of_injective e he` as an intermediate fact. Simplify using `only [Fintype.card_fin] at this`. Conclude with `this` after adjusting the coercions. Establish `h1 : diagonal (fun a => j (e a)) * G.submatrix e e = 1 + diagonal (fun a => j (e a)) * (G - diagonal j).submatrix e e`.

Use extensionality with `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Apply the tactic sequence `rcases hj (e a) with h | h <;> simp [h]`. Simplify using `[h, he.eq_iff, diagonal_apply]`.

Establish `h2` using `norm_det_one_add_sub_one_le_exp (diagonal (fun a => j (e a)) * (G - diagonal j).submatrix e e) hε (fun a b => by`. Rewrite using `[diagonal_mul, norm_mul, submatrix_apply]`. Apply the tactic sequence `rcases hj (e a) with h | h <;> simpa [h] using hG _ _)`. Rewrite `h2` using `[← h1, det_mul, det_diagonal, Fintype.card_fin]`. Establish `h3 : (i : ℝ) * (i * ε) ≤ (r : ℝ) ^ 2 * ε`.

Rewrite using `[sq, mul_assoc]`. Use `gcongr`. Establish `h4` using `Real.exp_le_exp.2 h3`. Establish `h0 : 0 ≤ (r : ℝ) ^ 2 * ε` using `by positivity`. Establish `h5` using `Real.abs_exp_sub_one_le (x := (r : ℝ) ^ 2 * ε) (by rwa [abs_of_nonneg h0])`.

Rewrite `h5` using `[abs_of_nonneg h0]`. Combine the linear relations using `[le_abs_self (Real.exp ((r : ℝ) ^ 2 * ε) - 1)]`.
-/
theorem norm_prod_sign_mul_det_submatrix_sub_one_le {r : ℕ} (j : Fin r → ℂ)
    (hj : ∀ a, j a = 1 ∨ j a = -1) (G : Matrix (Fin r) (Fin r) ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hG : ∀ a b, ‖(G - diagonal j) a b‖ ≤ ε) (hr : (r : ℝ) ^ 2 * ε ≤ 1)
    {i : ℕ} {e : Fin i → Fin r} (he : Function.Injective e) :
    ‖(∏ a, j (e a)) * (G.submatrix e e).det - 1‖ ≤ 2 * ((r : ℝ) ^ 2 * ε) := by
  have hi : (i : ℝ) ≤ r := by
    have := Fintype.card_le_of_injective e he
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have h1 : diagonal (fun a => j (e a)) * G.submatrix e e =
      1 + diagonal (fun a => j (e a)) * (G - diagonal j).submatrix e e := by
    ext a b
    by_cases h : a = b
    · subst h
      rcases hj (e a) with h | h <;> simp [h]
    · simp [h, he.eq_iff, diagonal_apply]
  have h2 := norm_det_one_add_sub_one_le_exp
    (diagonal (fun a => j (e a)) * (G - diagonal j).submatrix e e) hε (fun a b => by
      rw [diagonal_mul, norm_mul, submatrix_apply]
      rcases hj (e a) with h | h <;> simpa [h] using hG _ _)
  rw [← h1, det_mul, det_diagonal, Fintype.card_fin] at h2
  have h3 : (i : ℝ) * (i * ε) ≤ (r : ℝ) ^ 2 * ε := by
    rw [sq, mul_assoc]; gcongr
  have h4 := Real.exp_le_exp.2 h3
  have h0 : 0 ≤ (r : ℝ) ^ 2 * ε := by positivity
  have h5 := Real.abs_exp_sub_one_le (x := (r : ℝ) ^ 2 * ε) (by rwa [abs_of_nonneg h0])
  rw [abs_of_nonneg h0] at h5
  linarith [le_abs_self (Real.exp ((r : ℝ) ^ 2 * ε) - 1)]

/- English proof (translation)
Establish `h0 : 0 ≤ t` using `by linarith [norm_nonneg (d - 1)]`. Establish `h1` using `abs_le.1 ((Complex.abs_re_le_norm _).trans hd)`. Rewrite `h1` using `[Complex.sub_re, Complex.one_re]`. Establish `h2` using `abs_le.1 ((abs_norm_sub_norm_le d 1).trans hd)`. Rewrite `h2` using `[norm_one]`.

Establish `hp : 0 < ‖d‖` using `by linarith`. Use `⟨by linarith, abs_le.2 ⟨?_, ?_⟩⟩` and prove the remaining obligations. Establish `h3` using `Real.one_sub_inv_le_log_of_pos hp`. Establish `h4 : ‖d‖⁻¹ ≤ 1 + 3 * t`. Rewrite using `[inv_le_iff_one_le_mul₀ hp]`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear relations using `[Real.log_le_sub_one_of_pos hp]`.
-/
theorem re_pos_and_abs_log_norm_le {d : ℂ} {t : ℝ} (ht : t ≤ 1 / 6) (hd : ‖d - 1‖ ≤ 2 * t) :
    0 < d.re ∧ |Real.log ‖d‖| ≤ 3 * t := by
  have h0 : 0 ≤ t := by linarith [norm_nonneg (d - 1)]
  have h1 := abs_le.1 ((Complex.abs_re_le_norm _).trans hd)
  rw [Complex.sub_re, Complex.one_re] at h1
  have h2 := abs_le.1 ((abs_norm_sub_norm_le d 1).trans hd)
  rw [norm_one] at h2
  have hp : 0 < ‖d‖ := by linarith
  refine ⟨by linarith, abs_le.2 ⟨?_, ?_⟩⟩
  · have h3 := Real.one_sub_inv_le_log_of_pos hp
    have h4 : ‖d‖⁻¹ ≤ 1 + 3 * t := by
      rw [inv_le_iff_one_le_mul₀ hp]
      nlinarith
    linarith
  · linarith [Real.log_le_sub_one_of_pos hp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, mul_apply, transpose_apply, map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Both sides reduce to the same expression.
-/
theorem gram_eq_transpose_mul_mul_map_star {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G x = xᵀ * G.map τ * x.map star := by
  ext a b
  simp only [gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, of_apply, mul_apply, transpose_apply, map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Establish `h : (x * A).map star = x.map star * A.map star` using `Matrix.map_mul (f := starRingEnd ℂ)`. Rewrite using `[gram_eq_transpose_mul_mul_map_star, gram_eq_transpose_mul_mul_map_star, h, transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem gram_mul_eq_transpose_mul_gram_mul {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x A : Matrix (Fin r) (Fin r) ℂ) : gram τ G (x * A) = Aᵀ * gram τ G x * A.map star := by
  have h : (x * A).map star = x.map star * A.map star :=
    Matrix.map_mul (f := starRingEnd ℂ)
  rw [gram_eq_transpose_mul_mul_map_star, gram_eq_transpose_mul_mul_map_star, h, transpose_mul]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
The claim follows from `|Real.log ‖dmin X.Gm (rmul x A) τ i‖| ≤ 9 * ((r : ℝ) ^ 2 * δ) := by set j : Fin r → ℂ := fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hjdef have hj : ∀ a, j a = 1 ∨ j a = -1 := fun a => by simp only [hjdef, sgn] split_ifs <;> simp have hj1 : ∀ a, ‖j a‖ = 1 := fun a => by rc …`.
-/
theorem dmin_rmul_near_one {r : ℕ} (X : Data E r) (x : Frame X.Ψ r)
    (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (A : Frame X.Ψ r) {δ : ℝ} (hδ : 0 ≤ δ) (hr : (r : ℝ) ^ 2 * δ ≤ 1 / 100)
    (hA : ∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ δ) :
    rmul x A ∈ X.dom ∧ ∀ τ i, dmin X.Gm (rmul x A) τ i ≠ 0 ∧
      |Real.log ‖dmin X.Gm (rmul x A) τ i‖| ≤ 9 * ((r : ℝ) ^ 2 * δ) := by
  set j : Fin r → ℂ := fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hjdef
  have hj : ∀ a, j a = 1 ∨ j a = -1 := fun a => by
    simp only [hjdef, sgn]
    split_ifs <;> simp
  have hj1 : ∀ a, ‖j a‖ = 1 := fun a => by rcases hj a with h | h <;> simp [h]
  have hrr : (r : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero r
  have hG : ∀ (τ : X.Ψ) a b, ‖(gram τ.1 X.Gm (mat (rmul x A) τ) - diagonal j) a b‖ ≤ 3 * δ := by
    intro τ a b
    have h1 : mat (rmul x A) τ = mat x τ * (1 + (mat A τ - 1)) := by
      rw [add_sub_cancel]; rfl
    rw [h1, gram_mul_eq_transpose_mul_gram_mul, hx]
    refine norm_gram_sign_sub_le j hj1 _ hδ (by nlinarith) (fun a b => ?_) a b
    simpa [mat, one_apply] using hA τ a b
  have hmin : ∀ (τ : X.Ψ) {i : ℕ} {e : Fin i → Fin r}, Function.Injective e →
      0 < ((∏ a, j (e a)) * ((gram τ.1 X.Gm (mat (rmul x A) τ)).submatrix e e).det).re ∧
      |Real.log ‖(∏ a, j (e a)) * ((gram τ.1 X.Gm (mat (rmul x A) τ)).submatrix e e).det‖| ≤
        3 * ((r : ℝ) ^ 2 * (3 * δ)) := fun τ i e he =>
    re_pos_and_abs_log_norm_le (by linarith)
      (norm_prod_sign_mul_det_submatrix_sub_one_le j hj _ (by positivity) (hG τ) (by linarith) he)
  refine ⟨fun τ => ⟨fun h0 => ?_, fun i => ?_⟩, fun τ i => ?_⟩
  · have h := (hmin τ Function.injective_id).1
    rw [submatrix_id_id, gram_eq_transpose_mul_mul_map_star, det_mul, det_mul, det_transpose,
      h0] at h
    simp at h
  · have h := (hmin τ (Fin.castLE_injective (Nat.le_of_lt_succ i.isLt))).1
    have h1 : (∏ a, j (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) = ((psgn X.p0 i : ℝ) : ℂ) := by
      rw [psgn, Finset.prod_range, Complex.ofReal_prod]
      rfl
    rw [h1, Complex.re_ofReal_mul] at h
    exact h
  · obtain ⟨h1, h2⟩ := hmin τ (Fin.castLE_injective (Nat.le_of_lt_succ i.isLt))
    refine ⟨fun h0 => ?_, ?_⟩
    · rw [dmin, lminor] at h0
      rw [h0] at h1
      simp at h1
    · rw [norm_mul, norm_prod, Finset.prod_eq_one (fun a _ => hj1 _), one_mul] at h2
      rw [dmin, lminor]
      linarith

/- English proof (translation)
Use `⟨∑ τ, ∑ i : Fin r, Real.log ‖dmin X.Gm y τ i.succ / dmin X.Gm y τ i.castSucc‖ * (-(la τ i : ℝ) / 2), ?_, fun P => ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `(Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `hy τ i.succ`. Take `⟨h3, h4⟩` from `hy τ i.castSucc`. Rewrite using `[norm_div, Real.log_div (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h3), abs_mul, abs_div, abs_neg, abs_two]`. Establish `h5` using `abs_sub (Real.log ‖dmin X.Gm y τ i.succ‖) (Real.log ‖dmin X.Gm y τ i.castSucc‖)`. Use polynomial arithmetic with `[abs_nonneg (la τ i : ℝ)]`.

Rewrite using `[Data.pnorm, Real.exp_sum]`. Use `congr 1`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Real.exp_sum]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Conclude with `Real.rpow_def_of_pos (norm_pos_iff.2 (div_ne_zero (hy τ _).1 (hy τ _).1)) _`.
-/
theorem exists_pnorm_eq_mul_exp {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (y : Frame X.Ψ r) {t : ℝ}
    (hy : ∀ τ i, dmin X.Gm y τ i ≠ 0 ∧ |Real.log ‖dmin X.Gm y τ i‖| ≤ t) :
    ∃ s : ℝ, |s| ≤ t * ∑ τ, ∑ i, |(la τ i : ℝ)| ∧
      ∀ P : Frame X.Ψ r → ℂ, X.pnorm la P y = ‖P y‖ * Real.exp s := by
  refine ⟨∑ τ, ∑ i : Fin r, Real.log ‖dmin X.Gm y τ i.succ / dmin X.Gm y τ i.castSucc‖ *
    (-(la τ i : ℝ) / 2), ?_, fun P => ?_⟩
  · rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    obtain ⟨h1, h2⟩ := hy τ i.succ
    obtain ⟨h3, h4⟩ := hy τ i.castSucc
    rw [norm_div, Real.log_div (norm_ne_zero_iff.2 h1) (norm_ne_zero_iff.2 h3), abs_mul, abs_div,
      abs_neg, abs_two]
    have h5 := abs_sub (Real.log ‖dmin X.Gm y τ i.succ‖) (Real.log ‖dmin X.Gm y τ i.castSucc‖)
    nlinarith [abs_nonneg (la τ i : ℝ)]
  · rw [Data.pnorm, Real.exp_sum]
    congr 1
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact Real.rpow_def_of_pos (norm_pos_iff.2 (div_ne_zero (hy τ _).1 (hy τ _).1)) _

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Use function extensionality and compare the values at `τ a b`. Simplify using `[rmul, mat, mul_apply]`.
-/
theorem rmul_one_frame {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) :
    rmul x (fun _ a b => if a = b then 1 else 0) = x := by
  funext τ a b
  simp [rmul, mat, mul_apply]

omit [NumberField E] [IsCMField E] in
/- English proof (translation)
Use `differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_` and prove the remaining obligations. Establish `: (fun z : Frame Ψ r => rmul x (I + z) τ a b) = fun z => ∑ k, x τ a k * (I τ k b + z τ k b)`. Use function extensionality and compare the values at `z`. Simplify using `[rmul, mat, mul_apply]`. Rewrite using `[this]`.

Use `fun_prop`.
-/
theorem differentiable_rmul_add {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x I : Frame Ψ r) :
    Differentiable ℂ fun z : Frame Ψ r => rmul x (I + z) := by
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
  have : (fun z : Frame Ψ r => rmul x (I + z) τ a b) =
      fun z => ∑ k, x τ a k * (I τ k b + z τ k b) := by
    funext z
    simp [rmul, mat, mul_apply]
  rw [this]
  fun_prop

/- English proof (translation)
Use `set L : ℝ := ∑ τ, ∑ i, |(la τ i : ℝ)| with hL`. Establish `hL0 : 0 ≤ L` using `by positivity`. Use `set I : Frame X.Ψ r := fun _ a b => if a = b then 1 else 0 with hI`. Establish `hxI : rmul x I = x` using `rmul_one_frame x`. Take `⟨hxd, hx0⟩` from `dmin_rmul_near_one X x hx I le_rfl (by norm_num) (by simp [hI])`.

Rewrite `hxd`, `hx0` using `[hxI]`. Take `⟨s0, hs0, hs0'⟩` from `exists_pnorm_eq_mul_exp X la x hx0`. Establish `hPx : X.pnorm la P x = ‖P x‖`. Establish `: s0 = 0` using `by simpa using hs0`. Rewrite using `[hs0', this, Real.exp_zero, mul_one]`.

Establish `hSx` using `hS x hxd`. Rewrite `hSx`, `hhalf` using `[hPx]`. Establish `hS0 : 0 ≤ S` using `(norm_nonneg _).trans hSx`. Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases. Establish `: rmul x A = x` using `Subsingleton.elim _ _`.

Rewrite using `[this, hPx]`. Conclude with `⟨hxd, by linarith⟩`. Establish `hr' : (0 : ℝ) < r` using `by exact_mod_cast hr`. Take `⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (100 * (r : ℝ) ^ 2 * (1 + L))` from `⟨_, rfl⟩`. Establish `hδ0 : 0 < δ` using `by rw [hδ]; positivity`.

Establish `hδ1 : (r : ℝ) ^ 2 * δ * (1 + L) = 1 / 100` using `by rw [hδ]; field_simp`. Establish `hδ2 : 1 / (1000 * (r : ℝ) ^ 2 * (1 + L)) = δ / 10` using `by rw [hδ]; field_simp; norm_num`. Rewrite `hA` using `[hδ2]`. Establish `hrδ : 0 ≤ (r : ℝ) ^ 2 * δ` using `by positivity`. Establish `key : ∀ z : Frame X.Ψ r, ‖z‖ ≤ δ → rmul x (I + z) ∈ X.dom ∧ ∃ s : ℝ, |s| ≤ 0.09 ∧ X.pnorm la P (rmul x (I + z)) = ‖P (rmul x (I + z))‖ * Real.exp s`.

Introduce `z hz`. Take `⟨h1, h2⟩` from `dmin_rmul_near_one X x hx (I + z) hδ0.le (by nlinarith) (fun τ a b => by`. Simplify using `only [hI, Pi.add_apply, add_sub_cancel_left]`. Conclude with `(norm_le_pi_norm (z τ a) b).trans ((norm_le_pi_norm (z τ) a).trans ((norm_le_pi_norm z τ).trans hz)))`. Take `⟨s, hs, hs'⟩` from `exists_pnorm_eq_mul_exp X la _ h2`.

Conclude with `⟨h1, s, hs.trans (by rw [← hL]; nlinarith), hs' P⟩`. Establish `hexp : ∀ s : ℝ, |s| ≤ 0.09 → 0.91 ≤ Real.exp s` using `fun s hs => by`. Combine the linear relations using `[Real.add_one_le_exp s, (abs_le.1 hs).1]`. Establish `hsch` using `schwarz_ball_bound (Frame X.Ψ r) (fun z => P (rmul x (I + z))) δ (2.1 * S) hδ0 (hP.comp (differentiable_rmul_add x I).differentiableOn fun z hz => (key z (mem_ball_zero_iff.1 hz).le).1) (fun z hz => by`. Take `⟨h1, s, h2, h3⟩` from `key z (mem_ball_zero_iff.1 hz).le`.

Establish `h4` using `hS _ h1`. Establish `h5` using `hexp s h2`. Simplify using `only [add_zero, hxI]`. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Use polynomial arithmetic with `[norm_nonneg (P (rmul x (I + z)))])`.

Establish `hz : ‖A - I‖ ≤ δ / 10`. Establish `h0 : 0 ≤ δ / 10` using `by positivity`. Conclude with `(pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun a => (pi_norm_le_iff_of_nonneg h0).2 fun b => hA τ a b`. Take `⟨h1, s, h2, h3⟩` from `key (A - I) (by linarith)`. Establish `h4` using `hsch (A - I) (mem_ball_zero_iff.2 (by linarith))`.

Simplify using `only [add_zero, hxI] at h4`. Rewrite `h1`, `h3`, `h4` using `[add_sub_cancel]`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `h5 : 2.1 * S * ‖A - I‖ / δ ≤ 0.21 * S`. Rewrite using `[div_le_iff₀ hδ0]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `h6` using `hexp s h2`. Establish `h7` using `norm_le_insert (P (rmul x A)) (P x)`. Rewrite using `[h3]`. Use polynomial arithmetic with `[norm_nonneg (P (rmul x A))]`.
-/
theorem pnorm_near_half_max {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : DifferentiableOn ℂ P X.dom) (S : ℝ)
    (hS : ∀ x ∈ X.dom, X.pnorm la P x ≤ S) (x : Frame X.Ψ r)
    (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (hhalf : S / 2 ≤ X.pnorm la P x)
    (A : Frame X.Ψ r) (hA : ∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ 1 / (1000 * (r : ℝ) ^ 2 * (1 + ∑ τ, ∑ i, |(la τ i : ℝ)|))) :
    rmul x A ∈ X.dom ∧ S / 4 ≤ X.pnorm la P (rmul x A) := by
  set L : ℝ := ∑ τ, ∑ i, |(la τ i : ℝ)| with hL
  have hL0 : 0 ≤ L := by positivity
  set I : Frame X.Ψ r := fun _ a b => if a = b then 1 else 0 with hI
  have hxI : rmul x I = x := rmul_one_frame x
  obtain ⟨hxd, hx0⟩ := dmin_rmul_near_one X x hx I le_rfl (by norm_num) (by simp [hI])
  rw [hxI] at hxd hx0
  obtain ⟨s0, hs0, hs0'⟩ := exists_pnorm_eq_mul_exp X la x hx0
  have hPx : X.pnorm la P x = ‖P x‖ := by
    have : s0 = 0 := by simpa using hs0
    rw [hs0', this, Real.exp_zero, mul_one]
  have hSx := hS x hxd
  rw [hPx] at hSx hhalf
  have hS0 : 0 ≤ S := (norm_nonneg _).trans hSx
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have : rmul x A = x := Subsingleton.elim _ _
    rw [this, hPx]
    exact ⟨hxd, by linarith⟩
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = 1 / (100 * (r : ℝ) ^ 2 * (1 + L)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hδ1 : (r : ℝ) ^ 2 * δ * (1 + L) = 1 / 100 := by rw [hδ]; field_simp
  have hδ2 : 1 / (1000 * (r : ℝ) ^ 2 * (1 + L)) = δ / 10 := by rw [hδ]; field_simp; norm_num
  rw [hδ2] at hA
  have hrδ : 0 ≤ (r : ℝ) ^ 2 * δ := by positivity
  have key : ∀ z : Frame X.Ψ r, ‖z‖ ≤ δ → rmul x (I + z) ∈ X.dom ∧
      ∃ s : ℝ, |s| ≤ 0.09 ∧ X.pnorm la P (rmul x (I + z)) = ‖P (rmul x (I + z))‖ * Real.exp s := by
    intro z hz
    obtain ⟨h1, h2⟩ := dmin_rmul_near_one X x hx (I + z) hδ0.le (by nlinarith) (fun τ a b => by
      simp only [hI, Pi.add_apply, add_sub_cancel_left]
      exact (norm_le_pi_norm (z τ a) b).trans ((norm_le_pi_norm (z τ) a).trans
        ((norm_le_pi_norm z τ).trans hz)))
    obtain ⟨s, hs, hs'⟩ := exists_pnorm_eq_mul_exp X la _ h2
    exact ⟨h1, s, hs.trans (by rw [← hL]; nlinarith), hs' P⟩
  have hexp : ∀ s : ℝ, |s| ≤ 0.09 → 0.91 ≤ Real.exp s := fun s hs => by
    linarith [Real.add_one_le_exp s, (abs_le.1 hs).1]
  have hsch := schwarz_ball_bound (Frame X.Ψ r) (fun z => P (rmul x (I + z))) δ (2.1 * S) hδ0
    (hP.comp (differentiable_rmul_add x I).differentiableOn fun z hz =>
      (key z (mem_ball_zero_iff.1 hz).le).1)
    (fun z hz => by
      obtain ⟨h1, s, h2, h3⟩ := key z (mem_ball_zero_iff.1 hz).le
      have h4 := hS _ h1
      have h5 := hexp s h2
      simp only [add_zero, hxI]
      refine (norm_sub_le _ _).trans ?_
      nlinarith [norm_nonneg (P (rmul x (I + z)))])
  have hz : ‖A - I‖ ≤ δ / 10 := by
    have h0 : 0 ≤ δ / 10 := by positivity
    exact (pi_norm_le_iff_of_nonneg h0).2 fun τ => (pi_norm_le_iff_of_nonneg h0).2 fun a =>
      (pi_norm_le_iff_of_nonneg h0).2 fun b => hA τ a b
  obtain ⟨h1, s, h2, h3⟩ := key (A - I) (by linarith)
  have h4 := hsch (A - I) (mem_ball_zero_iff.2 (by linarith))
  simp only [add_zero, hxI] at h4
  rw [add_sub_cancel] at h1 h3 h4
  refine ⟨h1, ?_⟩
  have h5 : 2.1 * S * ‖A - I‖ / δ ≤ 0.21 * S := by
    rw [div_le_iff₀ hδ0]
    nlinarith
  have h6 := hexp s h2
  have h7 := norm_le_insert (P (rmul x A)) (P x)
  rw [h3]
  nlinarith [norm_nonneg (P (rmul x A))]

end GlobalTheory
