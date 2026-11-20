import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CumulantLowerBoundOfBoundedCentredStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorExpHermitianEqConvexExpSumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivLeadMinorExpHermitianZeroDiagStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsSumEigenvaluesNoncompactPartLeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HsLeWeightedSumBlockVariancesOfGapStatement
open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory.MinorDecay

/- English proof (translation)
Unfold `Jm`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma Jm_sq {n : ℕ} (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  split_ifs <;> simp

/- English proof (translation)
Take `⟨h1, h2⟩` from `h`. Unfold `inG at h1`. Establish `h3 : Xᴴ * Jm ε = X * Jm ε`. Rewrite using `[h2]`. Conclude with `eq_neg_of_add_eq_zero_left h1`.

Establish `h4` using `congrArg (· * Jm ε) h3`. Simplify using `only [Matrix.mul_assoc, Jm_sq, Matrix.mul_one] at h4`. Conclude with `h4`.
-/
lemma herm_of_inP {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X) :
    X.IsHermitian := by
  obtain ⟨h1, h2⟩ := h
  unfold inG at h1
  have h3 : Xᴴ * Jm ε = X * Jm ε := by
    rw [h2]; exact eq_neg_of_add_eq_zero_left h1
  have h4 := congrArg (· * Jm ε) h3
  simp only [Matrix.mul_assoc, Jm_sq, Matrix.mul_one] at h4
  exact h4

/- English proof (translation)
Establish `h2` using `congrFun (congrFun h.2 a) a`. Unfold `Jm at h2`. Simplify using `only [mul_diagonal, Matrix.neg_apply, diagonal_mul] at h2`. Use `split_ifs at h2`. Take the linear combination `h2 / 2`.

Take the linear combination `-h2 / 2`.
-/
lemma diag_of_inP {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X)
    (a : Fin n) : X a a = 0 := by
  have h2 := congrFun (congrFun h.2 a) a
  unfold Jm at h2
  simp only [mul_diagonal, Matrix.neg_apply, diagonal_mul] at h2
  split_ifs at h2
  · linear_combination h2 / 2
  · linear_combination -h2 / 2

/- English proof (translation)
Unfold `hs`. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply]`. Use `push_cast`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Complex.mul_conj']`.

Both sides reduce to the same expression.
-/
lemma hs_eq_trace {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    ((hs X : ℝ) : ℂ) = (X * Xᴴ).trace := by
  unfold hs
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, conjTranspose_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.mul_conj']
  rfl

/- English proof (translation)
Take `⟨hu, hJ⟩` from `hk`. Establish `h1 : kᴴ * k = 1` using `(Matrix.mem_unitaryGroup_iff').1 hu`. Establish `h2 : k * kᴴ = 1` using `(Matrix.mem_unitaryGroup_iff).1 hu`. Establish `hinv : k⁻¹ = kᴴ` using `Matrix.inv_eq_left_inv h1`. Establish `hunit : IsUnit k` using `⟨⟨k, kᴴ, h2, h1⟩, rfl⟩`.

Establish `hH` using `herm_of_inP h`. Establish `hJ' : kᴴ * Jm ε = Jm ε * kᴴ`. Combine the equalities or inequalities in the displayed calculation. Establish `hanti : kᴴ * X * k * Jm ε = -(Jm ε * (kᴴ * X * k))`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[hJ]`. Use `_ = -(kᴴ * Jm ε * X * k) := by rw [h.2]; simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]`. Use `_ = _ := by rw [hJ']; simp only [Matrix.mul_assoc]`. Establish `hYH : (kᴴ * X * k)ᴴ = kᴴ * X * k`.

Rewrite using `[conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]`. Use `⟨?_, ?_, (Matrix.exp_conj' k X hunit).symm⟩` and prove the remaining obligations. Rewrite using `[hinv]`. Use `⟨?_, hanti⟩` and prove the remaining obligations. Unfold `inG`.

Rewrite using `[hYH, hanti, neg_add_cancel]`. Rewrite using `[hinv]`. Apply `Complex.ofReal_injective` to reduce the goal to its premises. Rewrite using `[hs_eq_trace, hs_eq_trace, hYH, hH.eq]`. Establish `: kᴴ * X * k * (kᴴ * X * k) = kᴴ * (X * (k * kᴴ) * X * k)`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[this, h2, Matrix.mul_one, trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one]`.
-/
lemma conj_facts {n : ℕ} {ε : Fin n → Bool} {X k : Matrix (Fin n) (Fin n) ℂ} (h : inP ε X)
    (hk : k ∈ Kset ε) :
    inP ε (k⁻¹ * X * k) ∧ hs (k⁻¹ * X * k) = hs X ∧
      k⁻¹ * NormedSpace.exp X * k = NormedSpace.exp (k⁻¹ * X * k) := by
  obtain ⟨hu, hJ⟩ := hk
  have h1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
  have h2 : k * kᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hu
  have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv h1
  have hunit : IsUnit k := ⟨⟨k, kᴴ, h2, h1⟩, rfl⟩
  have hH := herm_of_inP h
  have hJ' : kᴴ * Jm ε = Jm ε * kᴴ := by
    calc kᴴ * Jm ε = kᴴ * Jm ε * (k * kᴴ) := by rw [h2, Matrix.mul_one]
      _ = kᴴ * (Jm ε * k) * kᴴ := by simp only [Matrix.mul_assoc]
      _ = (kᴴ * k) * Jm ε * kᴴ := by rw [← hJ]; simp only [Matrix.mul_assoc]
      _ = Jm ε * kᴴ := by rw [h1, Matrix.one_mul]
  have hanti : kᴴ * X * k * Jm ε = -(Jm ε * (kᴴ * X * k)) := by
    calc kᴴ * X * k * Jm ε = kᴴ * (X * Jm ε) * k := by
          simp only [Matrix.mul_assoc]; rw [hJ]
      _ = -(kᴴ * Jm ε * X * k) := by rw [h.2]; simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]
      _ = _ := by rw [hJ']; simp only [Matrix.mul_assoc]
  have hYH : (kᴴ * X * k)ᴴ = kᴴ * X * k := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]
  refine ⟨?_, ?_, (Matrix.exp_conj' k X hunit).symm⟩
  · rw [hinv]
    refine ⟨?_, hanti⟩
    unfold inG
    rw [hYH, hanti, neg_add_cancel]
  · rw [hinv]
    apply Complex.ofReal_injective
    rw [hs_eq_trace, hs_eq_trace, hYH, hH.eq]
    have : kᴴ * X * k * (kᴴ * X * k) = kᴴ * (X * (k * kᴴ) * X * k) := by
      simp only [Matrix.mul_assoc]
    rw [this, h2, Matrix.mul_one, trace_mul_comm, Matrix.mul_assoc, h2, Matrix.mul_one]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Apply `HasDerivAt.deriv` to reduce the goal to its premises. Apply `HasDerivAt.fun_sum` to reduce the goal to its premises. Introduce `J _`. Use `(((hasDerivAt_id t).mul_const (y J)).exp).const_mul (w J)` as an intermediate fact.

Conclude with `this.congr_deriv (by simp only [id]; ring)`.
-/
lemma deriv_sum_exp {ι : Type} [Fintype ι] (w y : ι → ℝ) :
    deriv (fun t : ℝ => ∑ J, w J * Real.exp (t * y J)) =
      fun t : ℝ => ∑ J, (w J * y J) * Real.exp (t * y J) := by
  funext t
  apply HasDerivAt.deriv
  apply HasDerivAt.fun_sum
  intro J _
  have := (((hasDerivAt_id t).mul_const (y J)).exp).const_mul (w J)
  exact this.congr_deriv (by simp only [id]; ring)

/- English proof (translation)
Unfold `hs`. Check the signs of the components of the expression.
-/
lemma hs_nonneg {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs X := by
  unfold hs; positivity

/- English proof (translation)
Establish `hH` using `herm_of_inP h`. Take `⟨w, hw0, -, hw1, hw⟩` from `GlobalTheory.T.leadMinor_exp_hermitian_eq_convex_exp_sum n Y hH l hl`. Take `⟨hd1, hd2⟩` from `GlobalTheory.T.deriv_leadMinor_exp_hermitian_zeroDiag n Y hH (diag_of_inP h) l hl`. Establish `hrange` using `GlobalTheory.T.abs_sum_eigenvalues_noncompactPart_le n ε Y hH h`. Rewrite `hrange` using `[← hR]`.

Use `set y : Finset (Fin n) → ℝ := fun J => ∑ j ∈ J, hH.eigenvalues j with hy`. Establish `hfun : (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re) = fun t : ℝ => ∑ J, w J * Real.exp (t * y J)`. Use function extensionality and compare the values at `t`. Rewrite using `[hw t, Complex.ofReal_re]`. Rewrite `hd1`, `hd2` using `[hfun, deriv_sum_exp]`.

Rewrite `hd2` using `[deriv_sum_exp]`. Simplify using `only [zero_mul, Real.exp_zero, mul_one] at hd1 hd2`. Establish `hone` using `hw 1`. Simplify using `only [Complex.ofReal_one, one_smul, one_mul] at hone`. Rewrite using `[hone, Complex.ofReal_re, Complex.ofReal_im]`.

Establish `hpos : 0 < ∑ J, w J * Real.exp (y J)`. Establish `: ∃ J, w J ≠ 0`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Simplify using `[hc] at hw1`.

Take `⟨J, hJ⟩` from `this`. Conclude with `Finset.sum_pos' (fun J _ => mul_nonneg (hw0 J) (Real.exp_pos _).le) ⟨J, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hw0 J) hJ.symm) (Real.exp_pos _)⟩`. Use `⟨hpos, rfl, ?_⟩` and prove the remaining obligations. Establish `hR0 : 0 ≤ R` using `by rw [hR]; positivity`. Establish `hvar : ∑ J, w J * y J ^ 2 = ∑ a : Fin n, ∑ b : Fin n, if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0`.

Rewrite using `[← hd2]; refine Finset.sum_congr rfl fun J _ => by ring`. Rewrite using `[← hvar]`. Break down `hR0.eq_or_lt with h0 | h0` into its components or cases. Establish `hy0 : ∀ J, y J = 0` using `fun J => abs_nonpos_iff.1 (by rw [h0]; exact hrange J)`. Express the relevant statement in the definitionally equal form `_ ≤ Real.log (∑ J, w J * Real.exp (y J))`.

Simplify using `[hy0, hw1]`. Conclude with `GlobalTheory.T.quadratic_le_log_sum_exp_of_bounded_centred _ w y R h0 hw0 hw1 hd1 (fun J _ => hrange J)`.
-/
lemma minor_bound {n : ℕ} {ε : Fin n → Bool} {Y : Matrix (Fin n) (Fin n) ℂ} (h : inP ε Y)
    (R : ℝ) (hR : R = Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
      (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) * Real.sqrt (hs Y))
    (l : ℕ) (hl : l ≤ n) :
    0 < (leadMinor (NormedSpace.exp Y) l hl).re ∧ (leadMinor (NormedSpace.exp Y) l hl).im = 0 ∧
      min 1 (1 / R) * (∑ a : Fin n, ∑ b : Fin n,
        if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0) / 4
        ≤ Real.log (leadMinor (NormedSpace.exp Y) l hl).re := by
  have hH := herm_of_inP h
  obtain ⟨w, hw0, -, hw1, hw⟩ := GlobalTheory.T.leadMinor_exp_hermitian_eq_convex_exp_sum n Y hH l hl
  obtain ⟨hd1, hd2⟩ := GlobalTheory.T.deriv_leadMinor_exp_hermitian_zeroDiag n Y hH (diag_of_inP h) l hl
  have hrange := GlobalTheory.T.abs_sum_eigenvalues_noncompactPart_le n ε Y hH h
  rw [← hR] at hrange
  set y : Finset (Fin n) → ℝ := fun J => ∑ j ∈ J, hH.eigenvalues j with hy
  have hfun : (fun t : ℝ => (leadMinor (NormedSpace.exp ((t : ℂ) • Y)) l hl).re)
      = fun t : ℝ => ∑ J, w J * Real.exp (t * y J) := by
    funext t; rw [hw t, Complex.ofReal_re]
  rw [hfun, deriv_sum_exp] at hd1 hd2
  rw [deriv_sum_exp] at hd2
  simp only [zero_mul, Real.exp_zero, mul_one] at hd1 hd2
  have hone := hw 1
  simp only [Complex.ofReal_one, one_smul, one_mul] at hone
  rw [hone, Complex.ofReal_re, Complex.ofReal_im]
  have hpos : 0 < ∑ J, w J * Real.exp (y J) := by
    have : ∃ J, w J ≠ 0 := by
      by_contra hc
      push Not at hc
      simp [hc] at hw1
    obtain ⟨J, hJ⟩ := this
    exact Finset.sum_pos' (fun J _ => mul_nonneg (hw0 J) (Real.exp_pos _).le)
      ⟨J, Finset.mem_univ _, mul_pos (lt_of_le_of_ne (hw0 J) hJ.symm) (Real.exp_pos _)⟩
  refine ⟨hpos, rfl, ?_⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hvar : ∑ J, w J * y J ^ 2 = ∑ a : Fin n, ∑ b : Fin n,
        if l ≤ a.val ∧ b.val < l then ‖Y a b‖ ^ 2 else 0 := by
    rw [← hd2]; refine Finset.sum_congr rfl fun J _ => by ring
  rw [← hvar]
  rcases hR0.eq_or_lt with h0 | h0
  · have hy0 : ∀ J, y J = 0 := fun J => abs_nonpos_iff.1 (by rw [h0]; exact hrange J)
    change _ ≤ Real.log (∑ J, w J * Real.exp (y J))
    simp [hy0, hw1]
  · exact GlobalTheory.T.quadratic_le_log_sum_exp_of_bounded_centred _ w y R h0 hw0 hw1 hd1 (fun J _ => hrange J)

/- English proof (translation)
Rewrite using `[min_mul_of_nonneg _ _ hH, one_mul]`. Use `congr 1`. Break down `hH.eq_or_lt with h0 | h0` into its components or cases. Simplify using `[← h0]`. Establish `hs : 0 < Real.sqrt H` using `Real.sqrt_pos.2 h0`.

Establish `: H = Real.sqrt H * Real.sqrt H` using `(Real.mul_self_sqrt hH).symm`. Break down `eq_or_ne c 0 with hc | hc` into its components or cases. Simplify using `[hc]`. Rewrite using `[div_mul_eq_mul_div, one_mul, div_eq_div_iff (by positivity) hc]`. Take the linear combination `c * this`.
-/
lemma min_mul_eq (H c : ℝ) (hH : 0 ≤ H) :
    min 1 (1 / (c * Real.sqrt H)) * H = min H (Real.sqrt H / c) := by
  rw [min_mul_of_nonneg _ _ hH, one_mul]
  congr 1
  rcases hH.eq_or_lt with h0 | h0
  · simp [← h0]
  · have hs : 0 < Real.sqrt H := Real.sqrt_pos.2 h0
    have : H = Real.sqrt H * Real.sqrt H := (Real.mul_self_sqrt hH).symm
    rcases eq_or_ne c 0 with hc | hc
    · simp [hc]
    · rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff (by positivity) hc]
      linear_combination c * this

/- English proof (translation)
Introduce `n ε lam h X km hlam hgap hX hk`. Take `⟨hY, hhs, hexp⟩` from `conj_facts hX hk`. Rewrite using `[hexp, ← hhs]`. Use `set Y := km⁻¹ * X * km with hYdef`. Establish `key` using `minor_bound hY _ rfl`.

Use `⟨fun l hl => ⟨(key l hl).1, (key l hl).2.1⟩, ?_⟩` and prove the remaining obligations. Establish `hgs` using `GlobalTheory.T.hs_le_weighted_sum_blockVariances_of_gap n ε lam h Y hlam.1 hgap hY`. Rewrite using `[← min_mul_eq _ _ (hs_nonneg Y)]`. Use `set c := Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) with hc`. Use `set t := min 1 (1 / (c * Real.sqrt (hs Y))) with ht`.

Establish `ht0 : 0 ≤ t` using `le_min zero_le_one (by positivity)`. Rewrite using `[Finset.prod_congr rfl fun i _ => Real.rpow_def_of_pos (key _ _).1 _, ← Real.exp_sum, Real.exp_le_exp]`. Establish `h2` using `mul_le_mul_of_nonneg_left hgs (by positivity : 0 ≤ t / 4)`. Rewrite `h2` using `[Finset.mul_sum]`. Establish `h3 : -(h / 8) * (t * hs Y) = -(t / 4 * (h * hs Y / 2))` using `by ring`.

Rewrite using `[h3, le_neg]`. Use `h2.trans ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Establish `hlt : lam ⟨i.val + 1, by omega⟩ < lam ⟨i.val, by omega⟩` using `hlam.1 (by simp [Fin.lt_def])`.

Establish `hk` using `(key (i.val + 1) (by omega)).2.2`. Establish `hs0 : 0 ≤ lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1` using `by linarith`. Use `mul_le_mul_of_nonneg_left hk hs0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem prod_leadMinor_decay : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (X km : Matrix (Fin n) (Fin n) ℂ), IsHCParam lam → GapAtLeast ε lam h → inP ε X → km ∈ Kset ε → (∀ (l : ℕ) (hl : l ≤ n), 0 < (leadMinor (km⁻¹ * NormedSpace.exp X * km) l hl).re ∧ (leadMinor (km⁻¹ * NormedSpace.exp X * km) l hl).im = 0) ∧ ∏ i : Fin (n - 1), (leadMinor (km⁻¹ * NormedSpace.exp X * km) (i.val + 1) (by omega)).re ^ (-(lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1)) ≤ Real.exp (-(h / 8) * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card : ℕ) : ℝ)))) := by
  intro n ε lam h X km hlam hgap hX hk
  obtain ⟨hY, hhs, hexp⟩ := conj_facts hX hk
  rw [hexp, ← hhs]
  set Y := km⁻¹ * X * km with hYdef
  have key := minor_bound hY _ rfl
  refine ⟨fun l hl => ⟨(key l hl).1, (key l hl).2.1⟩, ?_⟩
  have hgs := GlobalTheory.T.hs_le_weighted_sum_blockVariances_of_gap n ε lam h Y hlam.1 hgap hY
  rw [← min_mul_eq _ _ (hs_nonneg Y)]
  set c := Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card
      (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) with hc
  set t := min 1 (1 / (c * Real.sqrt (hs Y))) with ht
  have ht0 : 0 ≤ t := le_min zero_le_one (by positivity)
  rw [Finset.prod_congr rfl fun i _ => Real.rpow_def_of_pos (key _ _).1 _, ← Real.exp_sum,
    Real.exp_le_exp]
  have h2 := mul_le_mul_of_nonneg_left hgs (by positivity : 0 ≤ t / 4)
  rw [Finset.mul_sum] at h2
  have h3 : -(h / 8) * (t * hs Y) = -(t / 4 * (h * hs Y / 2)) := by ring
  rw [h3, le_neg]
  refine h2.trans ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hlt : lam ⟨i.val + 1, by omega⟩ < lam ⟨i.val, by omega⟩ :=
    hlam.1 (by simp [Fin.lt_def])
  have hk := (key (i.val + 1) (by omega)).2.2
  have hs0 : 0 ≤ lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1 := by linarith
  have := mul_le_mul_of_nonneg_left hk hs0
  linarith

end GlobalTheory.MinorDecay
