import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.HeckeTheta.Decay

open GlobalTheory.HeckeTheta

/- English proof (translation)
Establish `h1 : x ^ k ≤ 1 + (x ^ 2) ^ k`. Break down `le_total x 1 with h | h` into its components or cases. Use `pow_le_one₀ (n := k) hx h` as an intermediate fact. Use `pow_nonneg (sq_nonneg x) k` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h' : x ^ k ≤ x ^ (2 * k)` using `pow_le_pow_right₀ h (by omega)`. Rewrite `h'` using `[pow_mul]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : (x ^ 2) ^ k ≤ (k.factorial : ℝ) * Real.exp (x ^ 2)`. Use `Real.pow_div_factorial_le_exp (x ^ 2) (sq_nonneg x) k` as an intermediate fact.

Establish `hf : (0:ℝ) < k.factorial` using `by positivity`. Rewrite `this` using `[div_le_iff₀ hf, mul_comm]`. Then use the resulting hypothesis. Establish `he` using `Real.exp_pos (-2 * Real.pi * x ^ 2)`. Establish `h3 : Real.exp (x ^ 2) * Real.exp (-2 * Real.pi * x ^ 2) ≤ Real.exp (-Real.pi * x ^ 2)`. Rewrite using `[← Real.exp_add]`.

Conclude with `Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, sq_nonneg x])`. Establish `h4 : Real.exp (-2 * Real.pi * x ^ 2) ≤ Real.exp (-Real.pi * x ^ 2)` using `Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, sq_nonneg x])`. Establish `hf0 : (0:ℝ) ≤ k.factorial` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `: (x ^ 2) ^ k * Real.exp (-2 * Real.pi * x ^ 2) ≤ ((k.factorial : ℝ) * Real.exp (x ^ 2)) * Real.exp (-2 * Real.pi * x ^ 2)` using `mul_le_mul_of_nonneg_right h2 he.le`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `_ ≤ Real.exp (-Real.pi * x ^ 2) + (k.factorial : ℝ) * Real.exp (-Real.pi * x ^ 2) := by`. Use `mul_le_mul_of_nonneg_left h3 hf0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = _ := by ring`.
-/
theorem pow_mul_exp_le (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ k * Real.exp (-2 * Real.pi * x ^ 2) ≤ (1 + (k.factorial : ℝ)) * Real.exp (-Real.pi * x ^ 2) := by
  have h1 : x ^ k ≤ 1 + (x ^ 2) ^ k := by
    rcases le_total x 1 with h | h
    · have := pow_le_one₀ (n := k) hx h
      have := pow_nonneg (sq_nonneg x) k
      linarith
    · have h' : x ^ k ≤ x ^ (2 * k) := pow_le_pow_right₀ h (by omega)
      rw [pow_mul] at h'
      linarith
  have h2 : (x ^ 2) ^ k ≤ (k.factorial : ℝ) * Real.exp (x ^ 2) := by
    have := Real.pow_div_factorial_le_exp (x ^ 2) (sq_nonneg x) k
    have hf : (0:ℝ) < k.factorial := by positivity
    rwa [div_le_iff₀ hf, mul_comm] at this
  have he := Real.exp_pos (-2 * Real.pi * x ^ 2)
  have h3 : Real.exp (x ^ 2) * Real.exp (-2 * Real.pi * x ^ 2) ≤ Real.exp (-Real.pi * x ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_gt_three, sq_nonneg x])
  have h4 : Real.exp (-2 * Real.pi * x ^ 2) ≤ Real.exp (-Real.pi * x ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, sq_nonneg x])
  have hf0 : (0:ℝ) ≤ k.factorial := by positivity
  calc x ^ k * Real.exp (-2 * Real.pi * x ^ 2)
      ≤ (1 + (x ^ 2) ^ k) * Real.exp (-2 * Real.pi * x ^ 2) := mul_le_mul_of_nonneg_right h1 he.le
    _ = Real.exp (-2 * Real.pi * x ^ 2) + (x ^ 2) ^ k * Real.exp (-2 * Real.pi * x ^ 2) := by ring
    _ ≤ Real.exp (-Real.pi * x ^ 2) + (k.factorial : ℝ) * (Real.exp (x ^ 2) * Real.exp (-2 * Real.pi * x ^ 2)) := by
        have : (x ^ 2) ^ k * Real.exp (-2 * Real.pi * x ^ 2)
            ≤ ((k.factorial : ℝ) * Real.exp (x ^ 2)) * Real.exp (-2 * Real.pi * x ^ 2) :=
          mul_le_mul_of_nonneg_right h2 he.le
        linarith
    _ ≤ Real.exp (-Real.pi * x ^ 2) + (k.factorial : ℝ) * Real.exp (-Real.pi * x ^ 2) := by
        have := mul_le_mul_of_nonneg_left h3 hf0
        linarith
    _ = _ := by ring

variable {I : Type} [Fintype I]

def gC (n : I → ℤ) : ℝ := ∏ i, (1 + ((n i).natAbs.factorial : ℝ))

/- English proof (translation)
The claim follows from `Finset.prod_nonneg fun i _ => by positivity`.
-/
theorem gC_nonneg (n : I → ℤ) : 0 ≤ gC n := Finset.prod_nonneg fun i _ => by positivity

/- English proof (translation)
Unfold `gauss gC`. Rewrite using `[norm_prod, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]`. Apply `Finset.prod_le_prod (fun i _ => norm_nonneg _)` to reduce the goal to its premises. Introduce `i _`. Rewrite using `[norm_mul, norm_hmon, Complex.norm_exp_ofReal]`.

Use `pow_mul_exp_le (n i).natAbs (norm_nonneg (w i))` as an intermediate fact. Use `this using 2` and compare the differences between its conclusion and the goal.
-/
theorem norm_gauss_le (n : I → ℤ) (w : I → ℂ) :
    ‖gauss n w‖ ≤ gC n * Real.exp (-Real.pi * ∑ i, ‖w i‖ ^ 2) := by
  unfold gauss gC
  rw [norm_prod, Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun i _ => norm_nonneg _)
  intro i _
  rw [norm_mul, norm_hmon, Complex.norm_exp_ofReal]
  have := pow_mul_exp_le (n i).natAbs (norm_nonneg (w i))
  convert this using 2

/- English proof (translation)
Unfold `dil`. Rewrite using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]`. Establish `: Real.exp (y i / 2) ^ 2 = Real.exp (y i)`. Rewrite using `[← Real.exp_nat_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.
-/
theorem norm_dil_sq (y : I → ℝ) (v : I → ℂ) (i : I) :
    ‖dil y v i‖ ^ 2 = Real.exp (y i) * ‖v i‖ ^ 2 := by
  unfold dil
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  have : Real.exp (y i / 2) ^ 2 = Real.exp (y i) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [this]

/- English proof (translation)
Establish `hv : ‖v‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2`. Establish `: ‖v‖ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2)`. Use `(pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_` and prove the remaining obligations. Use `(le_abs_self _).trans (Real.abs_le_sqrt ?_)` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_ge (y : I → ℝ) (v : I → ℂ) {τ : ℝ} (hτ : 0 ≤ τ) (hy : ∀ i, τ ≤ Real.exp (y i)) :
    τ * ‖v‖ ^ 2 ≤ ∑ i, Real.exp (y i) * ‖v i‖ ^ 2 := by
  have hv : ‖v‖ ^ 2 ≤ ∑ i, ‖v i‖ ^ 2 := by
    have : ‖v‖ ≤ Real.sqrt (∑ i, ‖v i‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
      exact Finset.single_le_sum (f := fun i => ‖v i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    calc ‖v‖ ^ 2 ≤ (Real.sqrt (∑ i, ‖v i‖ ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = _ := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  calc τ * ‖v‖ ^ 2 ≤ τ * ∑ i, ‖v i‖ ^ 2 := mul_le_mul_of_nonneg_left hv hτ
    _ = ∑ i, τ * ‖v i‖ ^ 2 := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hy i) (sq_nonneg _)

/- English proof (translation)
Use `(norm_gauss_le n _).trans ?_` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_left _ (gC_nonneg n)` to reduce the goal to its premises. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Repeatedly rewrite using `[norm_dil_sq]`. Use `mul_le_mul_of_nonneg_left (sum_ge y v hτ hy) Real.pi_pos.le` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_term_le (n : I → ℤ) (y : I → ℝ) (v : I → ℂ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hy : ∀ i, τ ≤ Real.exp (y i)) :
    ‖gauss n (dil y v)‖ ≤ gC n * Real.exp (-Real.pi * τ * ‖v‖ ^ 2) := by
  refine (norm_gauss_le n _).trans ?_
  apply mul_le_mul_of_nonneg_left _ (gC_nonneg n)
  apply Real.exp_le_exp.mpr
  simp_rw [norm_dil_sq]
  have := mul_le_mul_of_nonneg_left (sum_ge y v hτ hy) Real.pi_pos.le
  linarith

/- English proof (translation)
Apply the tactic sequence `unfold hmon; split_ifs <;> fun_prop`.
-/
theorem continuous_hmon (m : ℤ) : Continuous (hmon m) := by
  unfold hmon; split_ifs <;> fun_prop

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `y0`. Take `⟨L, hL⟩ : ∃ L : ℝ, ∀ i, -L < y0 i` from `⟨∑ i, |y0 i| + 1, fun i => by`. Use `Finset.single_le_sum (f := fun i => |y0 i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)` as an intermediate fact. Use `neg_abs_le (y0 i)` as an intermediate fact.

Use the proof step `linarith⟩`. Set `U : Set (I → ℝ)` to `{y | ∀ i, -L < y i}`. Establish `hU : IsOpen U`. Simplify using `only [U, Set.setOf_forall]`. Conclude with `isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)`.

Establish `hc : ContinuousOn (theta e a n) U`. Unfold `theta`. Use `continuousOn_tsum (u := fun j => gC n * (‖a j‖ * Real.exp (-(Real.pi * Real.exp (-L)) * ‖e j‖ ^ 2))) (fun j => ?_) ?_ ?_` and prove the remaining obligations. Apply `Continuous.continuousOn` to reduce the goal to its premises. Apply `continuous_const.mul` to reduce the goal to its premises.

Unfold `gauss`. Use `continuous_finset_prod _ fun i _ => ?_` and prove the remaining obligations. Establish `hd : Continuous fun y : I → ℝ => dil y (e j) i` using `by unfold dil; fun_prop`. Conclude with `((continuous_hmon _).comp hd).mul (by fun_prop)`. Conclude with `(ha _ (by positivity)).mul_left _`.

Introduce `j y hy`. Rewrite using `[norm_mul]`. Establish `h` using `norm_term_le n y (e j) (Real.exp_pos (-L)).le fun i => Real.exp_le_exp.mpr (hy i).le`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hc.continuousAt (hU.mem_nhds hL)`.
-/
theorem continuous_theta {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ)
    (ha : ∀ ε : ℝ, 0 < ε → Summable (fun j => ‖a j‖ * Real.exp (-ε * ‖e j‖ ^ 2))) :
    Continuous (theta e a n) := by
  rw [continuous_iff_continuousAt]
  intro y0
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ i, -L < y0 i := ⟨∑ i, |y0 i| + 1, fun i => by
      have := Finset.single_le_sum (f := fun i => |y0 i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
      have := neg_abs_le (y0 i)
      linarith⟩
  let U : Set (I → ℝ) := {y | ∀ i, -L < y i}
  have hU : IsOpen U := by
    simp only [U, Set.setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hc : ContinuousOn (theta e a n) U := by
    unfold theta
    refine continuousOn_tsum
      (u := fun j => gC n * (‖a j‖ * Real.exp (-(Real.pi * Real.exp (-L)) * ‖e j‖ ^ 2)))
      (fun j => ?_) ?_ ?_
    · apply Continuous.continuousOn
      apply continuous_const.mul
      unfold gauss
      refine continuous_finset_prod _ fun i _ => ?_
      have hd : Continuous fun y : I → ℝ => dil y (e j) i := by unfold dil; fun_prop
      exact ((continuous_hmon _).comp hd).mul (by fun_prop)
    · exact (ha _ (by positivity)).mul_left _
    · intro j y hy
      rw [norm_mul]
      have h := norm_term_le n y (e j) (Real.exp_pos (-L)).le fun i => Real.exp_le_exp.mpr (hy i).le
      calc ‖a j‖ * ‖gauss n (dil y (e j))‖
          ≤ ‖a j‖ * (gC n * Real.exp (-Real.pi * Real.exp (-L) * ‖e j‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h (norm_nonneg _)
        _ = _ := by ring_nf
  exact hc.continuousAt (hU.mem_nhds hL)

/- English proof (translation)
Establish `hK1 : 0 ≤ (|σ| + 1) ^ 2 / (2 * c)` using `by positivity`. Establish `hσ` using `abs_nonneg σ`. Break down `le_total 0 t with h | h` into its components or cases. Establish `he : t ^ 2 / 2 ≤ Real.exp t`. Use `Real.pow_div_factorial_le_exp t h 2` as an intermediate fact.

Simplify using `using this`. Rewrite using `[abs_of_nonneg h]`. Establish `hs : σ * t ≤ |σ| * t` using `mul_le_mul_of_nonneg_right (le_abs_self σ) h`. Establish `key : (|σ| + 1) * t - c * (t ^ 2 / 2) ≤ (|σ| + 1) ^ 2 / (2 * c)`. Rewrite using `[le_div_iff₀ (by positivity)]`.

Use polynomial arithmetic with `[sq_nonneg (c * t - (|σ| + 1))]`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left he hc.le]`. Rewrite using `[abs_of_nonpos h]`. Establish `hs : σ * t ≤ |σ| * R`. Combine the equalities or inequalities in the displayed calculation.

Use `mul_pos hc (Real.exp_pos t)` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_dim {σ c R t : ℝ} (hc : 0 < c) (hR : 0 ≤ R) (ht : -R ≤ t) :
    σ * t - c * Real.exp t ≤ ((|σ| + 1) ^ 2 / (2 * c) + (|σ| + 1) * R) - |t| := by
  have hK1 : 0 ≤ (|σ| + 1) ^ 2 / (2 * c) := by positivity
  have hσ := abs_nonneg σ
  rcases le_total 0 t with h | h
  · have he : t ^ 2 / 2 ≤ Real.exp t := by
      have := Real.pow_div_factorial_le_exp t h 2
      simpa using this
    rw [abs_of_nonneg h]
    have hs : σ * t ≤ |σ| * t := mul_le_mul_of_nonneg_right (le_abs_self σ) h
    have key : (|σ| + 1) * t - c * (t ^ 2 / 2) ≤ (|σ| + 1) ^ 2 / (2 * c) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (c * t - (|σ| + 1))]
    nlinarith [mul_le_mul_of_nonneg_left he hc.le]
  · rw [abs_of_nonpos h]
    have hs : σ * t ≤ |σ| * R := by
      calc σ * t ≤ |σ * t| := le_abs_self _
        _ = |σ| * |t| := abs_mul _ _
        _ ≤ |σ| * R := mul_le_mul_of_nonneg_left (by rw [abs_of_nonpos h]; linarith) hσ
    have := mul_pos hc (Real.exp_pos t)
    nlinarith

/- English proof (translation)
Establish `h1 : IntegrableOn (fun x : ℝ => Real.exp (-1 * |x|)) (Set.Ioi 0)` using `(exp_neg_integrableOn_Ioi 0 one_pos).congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi`. Establish `h2 : IntegrableOn (fun x : ℝ => Real.exp (-1 * |x|)) (Set.Iic 0)` using `(integrableOn_exp_mul_Iic one_pos 0).congr_fun (fun x hx => by rw [abs_of_nonpos hx, neg_mul_neg]) measurableSet_Iic`. Establish `h3` using `h2.union h1`. Rewrite `h3` using `[Set.Iic_union_Ioi, integrableOn_univ]`. Conclude with `h3`.
-/
theorem integrable_exp_neg_abs_one : Integrable (fun x : ℝ => Real.exp (-1 * |x|)) := by
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-1 * |x|)) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 one_pos).congr_fun (fun x hx => by rw [abs_of_pos hx]) measurableSet_Ioi
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-1 * |x|)) (Set.Iic 0) :=
    (integrableOn_exp_mul_Iic one_pos 0).congr_fun (fun x hx => by rw [abs_of_nonpos hx, neg_mul_neg])
      measurableSet_Iic
  have h3 := h2.union h1
  rw [Set.Iic_union_Ioi, integrableOn_univ] at h3
  exact h3

end GlobalTheory.HeckeTheta.Decay

namespace GlobalTheory.HeckeTheta.Decay

open GlobalTheory.HeckeTheta

/- English proof (translation)
Introduce `I _ ι e a n q B R hn ha hδ hq hqB hqR`. Take `⟨δ, hδ0, hδ⟩` from `hδ`. Take `⟨i0, hi0⟩` from `hn`. Use `haveI : Nonempty I := ⟨i0⟩`. Establish `hcont` using `continuous_theta e a n ha`.

Establish `hmeas : AEStronglyMeasurable (fun y => (q y : ℂ) * theta e a n y) volume` using `((Complex.measurable_ofReal.comp hq).mul hcont.measurable).aestronglyMeasurable`. Use `⟨hmeas, fun σ => ?_⟩` and prove the remaining obligations. Establish `hB : 0 ≤ B` using `(abs_nonneg _).trans (hqB 0)`. Use `set R' := max R 0 with hR'`. Establish `hR0 : 0 ≤ R'` using `le_max_right _ _`.

Establish `hqR' : ∀ y, q y ≠ 0 → ∀ i j, y i ≤ y j + R'` using `fun y hy i j => by`. Use `hqR y hy i j` as an intermediate fact. Use `le_max_left R 0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `set N : ℝ := (Fintype.card I : ℝ) with hN`.

Establish `hN0 : 0 < N` using `by rw [hN]; exact_mod_cast Fintype.card_pos`. Use `set τ0 : ℝ := Real.exp (-R') / N with hτ0`. Establish `hτ0p : 0 < τ0` using `by positivity`. Use `set ε0 : ℝ := Real.pi / 2 * τ0 with hε0`. Establish `hε0p : 0 < ε0` using `by positivity`.

Establish `hS` using `ha ε0 hε0p`. Use `set S : ℝ := ∑' j, ‖a j‖ * Real.exp (-ε0 * ‖e j‖ ^ 2) with hSdef`. Establish `hS0 : 0 ≤ S` using `tsum_nonneg fun j => by positivity`. Use `set c' : ℝ := Real.pi / 2 * δ ^ 2 * τ0 with hc'`. Establish `hc'p : 0 < c'` using `by positivity`.

Use `set K : ℝ := (|σ| + 1) ^ 2 / (2 * c') + (|σ| + 1) * R' with hK`. Use `set G : (I → ℝ) → ℝ := fun y => B * gC n * S * ∏ i, (Real.exp K * Real.exp (-1 * |y i|)) with hG`. Establish `htheta : ∀ y, q y ≠ 0 → 0 ≤ ∑ i, y i → ‖theta e a n y‖ ≤ gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * S`. Introduce `y hy hs`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, 0 ≤ y k := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Use `Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i (_ : i ∈ Finset.univ) => h i)` as an intermediate fact. Simplify using `only [Finset.sum_const_zero] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set T : ℝ := Real.exp (-R') * (∑ i, Real.exp (y i)) / N with hT`. Establish `hTi : ∀ i, T ≤ Real.exp (y i)`. Introduce `i`. Rewrite using `[hT, div_le_iff₀ hN0]`. Establish `h1 : ∀ j, Real.exp (-R') * Real.exp (y j) ≤ Real.exp (y i)` using `fun j => by`.

Rewrite using `[← Real.exp_add]; exact Real.exp_le_exp.mpr (by have := hqR' y hy j i; linarith)`. Combine the equalities or inequalities in the displayed calculation. Establish `hTτ : τ0 ≤ T`. Rewrite using `[hT, hτ0]`. Apply `div_le_div_of_nonneg_right _ hN0.le` to reduce the goal to its premises.

Establish `h1 : 1 ≤ ∑ i, Real.exp (y i)` using `(Real.one_le_exp hk).trans (Finset.single_le_sum (f := fun i => Real.exp (y i)) (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ k))`. Use `Real.exp_pos (-R')` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hT0 : 0 ≤ T` using `hτ0p.le.trans hTτ`. Establish `hterm : ∀ j, ‖a j * gauss n (dil y (e j))‖ ≤ gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * (‖a j‖ * Real.exp (-ε0 * ‖e j‖ ^ 2))`.

Introduce `j`. Establish `hC` using `gC_nonneg n`. Distinguish the cases in `haj : a j = 0`. Simplify using `only [haj, zero_mul, norm_zero, mul_zero]`. Conclude with `le_refl _`.

Distinguish the cases in `hej : e j = 0`. Establish `: dil y (e j) = 0` using `by funext i; simp [dil, hej]`. Rewrite using `[this, gauss_zero ⟨i0, hi0⟩, mul_zero, norm_zero]`. Check the signs of the components of the expression. Establish `hd` using `hδ j haj hej`.

Rewrite using `[norm_mul]`. Establish `h1` using `norm_term_le n y (e j) hT0 hTi`. Establish `h2 : Real.exp (-Real.pi * T * ‖e j‖ ^ 2) ≤ Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (-ε0 * ‖e j‖ ^ 2)`. Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises.

Establish `e1 : c' * ∑ i, Real.exp (y i) = Real.pi / 2 * δ ^ 2 * T`. Rewrite using `[hc', hT, hτ0]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hε0]`. Establish `hδe : δ ^ 2 ≤ ‖e j‖ ^ 2` using `pow_le_pow_left₀ hδ0.le hd 2`.

Establish `a1` using `mul_le_mul_of_nonneg_left hδe hT0`. Establish `a2` using `mul_le_mul_of_nonneg_right hTτ (sq_nonneg ‖e j‖)`. Establish `hp` using `Real.pi_pos`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left a1 hp.le, mul_le_mul_of_nonneg_left a2 hp.le, e1]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hsum : HasSum (fun j => gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * (‖a j‖ * Real.exp (-ε0 * ‖e j‖ ^ 2))) (gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * S)` using `hS.hasSum.mul_left _`. Conclude with `tsum_of_norm_bounded hsum hterm`. Establish `hbound : ∀ y, 0 ≤ ∑ i, y i → ‖(q y : ℂ) * theta e a n y‖ * Real.exp (σ * ∑ i, y i) ≤ G y`. Introduce `y hs`. Establish `hG0 : 0 ≤ G y`.

Simplify using `only [hG]`. Use `gC_nonneg n` as an intermediate fact. Check the signs of the components of the expression. Distinguish the cases in `hq0 : q y = 0`. Simplify using `only [hq0, Complex.ofReal_zero, zero_mul, norm_zero]`.

Conclude with `hG0`. Establish `hyR : ∀ i, -R' ≤ y i`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, 0 ≤ y k := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Use `Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i (_ : i ∈ Finset.univ) => h i)` as an intermediate fact. Simplify using `only [Finset.sum_const_zero] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `i`. Use `hqR' y hq0 k i` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `htheta y hq0 hs`. Establish `h2 : Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (σ * ∑ i, y i) ≤ ∏ i, (Real.exp K * Real.exp (-1 * |y i|))`. Rewrite using `[← Real.exp_add]`. Establish `e1 : -c' * ∑ i, Real.exp (y i) + σ * ∑ i, y i = ∑ i, (σ * y i - c' * Real.exp (y i))`.

Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[e1, Real.exp_sum]`. Apply `Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)` to reduce the goal to its premises. Introduce `i _`.

Rewrite using `[← Real.exp_add]`. Apply `Real.exp_le_exp.mpr` to reduce the goal to its premises. Use `one_dim (σ := σ) hc'p hR0 (hyR i)` as an intermediate fact. Rewrite using `[hK]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hqy : ‖(q y : ℂ)‖ ≤ B` using `by rw [Complex.norm_real, Real.norm_eq_abs]; exact hqB y`. Rewrite using `[norm_mul]`. Establish `hC` using `gC_nonneg n`. Combine the equalities or inequalities in the displayed calculation. Establish `hGi : Integrable G volume`.

Establish `h1 : Integrable (fun y : I → ℝ => ∏ i, (Real.exp K * Real.exp (-1 * |y i|))) volume` using `Integrable.fintype_prod (f := fun _ x => Real.exp K * Real.exp (-1 * |x|)) fun _ => integrable_exp_neg_abs_one.const_mul _`. Conclude with `h1.const_mul _`. Establish `hset : MeasurableSet {y : I → ℝ | 0 ≤ ∑ i, y i}` using `measurableSet_le measurable_const (by fun_prop)`. Use `Integrable.mono' hGi.restrict ?_ ?_` and prove the remaining obligations. Conclude with `(hmeas.norm.mul (Continuous.aestronglyMeasurable (by fun_prop))).restrict`.

Rewrite using `[ae_restrict_iff' hset] filter_upwards with y hy`. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Conclude with `hbound y hy`.
-/
theorem integrable_weight_theta : ∀ (I : Type) [Fintype I] {ι : Type} (e : ι → I → ℂ) (a : ι → ℂ) (n : I → ℤ) (q : (I → ℝ) → ℝ) (B R : ℝ), (∃ i, n i ≠ 0) → (∀ ε : ℝ, 0 < ε → Summable (fun j => ‖a j‖ * Real.exp (-ε * ‖e j‖ ^ 2))) → (∃ δ : ℝ, 0 < δ ∧ ∀ j, a j ≠ 0 → e j ≠ 0 → δ ≤ ‖e j‖) → Measurable q → (∀ y, |q y| ≤ B) → (∀ y, q y ≠ 0 → ∀ i j, y i - y j ≤ R) → MeasureTheory.AEStronglyMeasurable (fun y => (q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y) MeasureTheory.volume ∧ ∀ σ : ℝ, MeasureTheory.Integrable (fun y => ‖(q y : ℂ) * GlobalTheory.HeckeTheta.theta e a n y‖ * Real.exp (σ * ∑ i, y i)) (MeasureTheory.volume.restrict {y : I → ℝ | 0 ≤ ∑ i, y i}) := by
  intro I _ ι e a n q B R hn ha hδ hq hqB hqR
  obtain ⟨δ, hδ0, hδ⟩ := hδ
  obtain ⟨i0, hi0⟩ := hn
  haveI : Nonempty I := ⟨i0⟩
  have hcont := continuous_theta e a n ha
  have hmeas : AEStronglyMeasurable (fun y => (q y : ℂ) * theta e a n y) volume :=
    ((Complex.measurable_ofReal.comp hq).mul hcont.measurable).aestronglyMeasurable
  refine ⟨hmeas, fun σ => ?_⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hqB 0)
  set R' := max R 0 with hR'
  have hR0 : 0 ≤ R' := le_max_right _ _
  have hqR' : ∀ y, q y ≠ 0 → ∀ i j, y i ≤ y j + R' := fun y hy i j => by
    have := hqR y hy i j; have := le_max_left R 0; linarith
  set N : ℝ := (Fintype.card I : ℝ) with hN
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set τ0 : ℝ := Real.exp (-R') / N with hτ0
  have hτ0p : 0 < τ0 := by positivity
  set ε0 : ℝ := Real.pi / 2 * τ0 with hε0
  have hε0p : 0 < ε0 := by positivity
  have hS := ha ε0 hε0p
  set S : ℝ := ∑' j, ‖a j‖ * Real.exp (-ε0 * ‖e j‖ ^ 2) with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun j => by positivity
  set c' : ℝ := Real.pi / 2 * δ ^ 2 * τ0 with hc'
  have hc'p : 0 < c' := by positivity
  set K : ℝ := (|σ| + 1) ^ 2 / (2 * c') + (|σ| + 1) * R' with hK
  set G : (I → ℝ) → ℝ := fun y => B * gC n * S * ∏ i, (Real.exp K * Real.exp (-1 * |y i|)) with hG

  have htheta : ∀ y, q y ≠ 0 → 0 ≤ ∑ i, y i →
      ‖theta e a n y‖ ≤ gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * S := by
    intro y hy hs
    obtain ⟨k, hk⟩ : ∃ k, 0 ≤ y k := by
      by_contra h
      push_neg at h
      have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i (_ : i ∈ Finset.univ) => h i)
      simp only [Finset.sum_const_zero] at this
      linarith
    set T : ℝ := Real.exp (-R') * (∑ i, Real.exp (y i)) / N with hT
    have hTi : ∀ i, T ≤ Real.exp (y i) := by
      intro i
      rw [hT, div_le_iff₀ hN0]
      have h1 : ∀ j, Real.exp (-R') * Real.exp (y j) ≤ Real.exp (y i) := fun j => by
        rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by have := hqR' y hy j i; linarith)
      calc Real.exp (-R') * ∑ j, Real.exp (y j) = ∑ j, Real.exp (-R') * Real.exp (y j) := Finset.mul_sum _ _ _
        _ ≤ ∑ _j : I, Real.exp (y i) := Finset.sum_le_sum fun j _ => h1 j
        _ = Real.exp (y i) * N := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN, mul_comm]
    have hTτ : τ0 ≤ T := by
      rw [hT, hτ0]
      apply div_le_div_of_nonneg_right _ hN0.le
      have h1 : 1 ≤ ∑ i, Real.exp (y i) :=
        (Real.one_le_exp hk).trans (Finset.single_le_sum (f := fun i => Real.exp (y i))
          (fun i _ => (Real.exp_pos _).le) (Finset.mem_univ k))
      have := Real.exp_pos (-R')
      nlinarith
    have hT0 : 0 ≤ T := hτ0p.le.trans hTτ
    have hterm : ∀ j, ‖a j * gauss n (dil y (e j))‖ ≤
        gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * (‖a j‖ * Real.exp (-ε0 * ‖e j‖ ^ 2)) := by
      intro j
      have hC := gC_nonneg n
      by_cases haj : a j = 0
      · simp only [haj, zero_mul, norm_zero, mul_zero]; exact le_refl _
      by_cases hej : e j = 0
      · have : dil y (e j) = 0 := by funext i; simp [dil, hej]
        rw [this, gauss_zero ⟨i0, hi0⟩, mul_zero, norm_zero]
        positivity
      have hd := hδ j haj hej
      rw [norm_mul]
      have h1 := norm_term_le n y (e j) hT0 hTi
      have h2 : Real.exp (-Real.pi * T * ‖e j‖ ^ 2) ≤
          Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (-ε0 * ‖e j‖ ^ 2) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have e1 : c' * ∑ i, Real.exp (y i) = Real.pi / 2 * δ ^ 2 * T := by
          rw [hc', hT, hτ0]; field_simp
        rw [hε0]
        have hδe : δ ^ 2 ≤ ‖e j‖ ^ 2 := pow_le_pow_left₀ hδ0.le hd 2
        have a1 := mul_le_mul_of_nonneg_left hδe hT0
        have a2 := mul_le_mul_of_nonneg_right hTτ (sq_nonneg ‖e j‖)
        have hp := Real.pi_pos
        nlinarith [mul_le_mul_of_nonneg_left a1 hp.le, mul_le_mul_of_nonneg_left a2 hp.le, e1]
      calc ‖a j‖ * ‖gauss n (dil y (e j))‖ ≤ ‖a j‖ * (gC n * Real.exp (-Real.pi * T * ‖e j‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ ‖a j‖ * (gC n * (Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (-ε0 * ‖e j‖ ^ 2))) := by
            gcongr
        _ = _ := by ring
    have hsum : HasSum (fun j => gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) *
        (‖a j‖ * Real.exp (-ε0 * ‖e j‖ ^ 2))) (gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * S) :=
      hS.hasSum.mul_left _
    exact tsum_of_norm_bounded hsum hterm
  have hbound : ∀ y, 0 ≤ ∑ i, y i →
      ‖(q y : ℂ) * theta e a n y‖ * Real.exp (σ * ∑ i, y i) ≤ G y := by
    intro y hs
    have hG0 : 0 ≤ G y := by
      simp only [hG]
      have := gC_nonneg n
      positivity
    by_cases hq0 : q y = 0
    · simp only [hq0, Complex.ofReal_zero, zero_mul, norm_zero]; exact hG0
    have hyR : ∀ i, -R' ≤ y i := by
      obtain ⟨k, hk⟩ : ∃ k, 0 ≤ y k := by
        by_contra h
        push_neg at h
        have := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i (_ : i ∈ Finset.univ) => h i)
        simp only [Finset.sum_const_zero] at this
        linarith
      intro i; have := hqR' y hq0 k i; linarith
    have h1 := htheta y hq0 hs
    have h2 : Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (σ * ∑ i, y i) ≤
        ∏ i, (Real.exp K * Real.exp (-1 * |y i|)) := by
      rw [← Real.exp_add]
      have e1 : -c' * ∑ i, Real.exp (y i) + σ * ∑ i, y i = ∑ i, (σ * y i - c' * Real.exp (y i)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [e1, Real.exp_sum]
      apply Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le)
      intro i _
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := one_dim (σ := σ) hc'p hR0 (hyR i)
      rw [hK]; linarith
    have hqy : ‖(q y : ℂ)‖ ≤ B := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hqB y
    rw [norm_mul]
    have hC := gC_nonneg n
    calc ‖(q y : ℂ)‖ * ‖theta e a n y‖ * Real.exp (σ * ∑ i, y i)
        ≤ B * (gC n * Real.exp (-c' * ∑ i, Real.exp (y i)) * S) * Real.exp (σ * ∑ i, y i) := by
          gcongr
      _ = B * gC n * S * (Real.exp (-c' * ∑ i, Real.exp (y i)) * Real.exp (σ * ∑ i, y i)) := by ring
      _ ≤ B * gC n * S * ∏ i, (Real.exp K * Real.exp (-1 * |y i|)) := by
          gcongr
  have hGi : Integrable G volume := by
    have h1 : Integrable (fun y : I → ℝ => ∏ i, (Real.exp K * Real.exp (-1 * |y i|))) volume :=
      Integrable.fintype_prod (f := fun _ x => Real.exp K * Real.exp (-1 * |x|))
        fun _ => integrable_exp_neg_abs_one.const_mul _
    exact h1.const_mul _
  have hset : MeasurableSet {y : I → ℝ | 0 ≤ ∑ i, y i} :=
    measurableSet_le measurable_const (by fun_prop)
  refine Integrable.mono' hGi.restrict ?_ ?_
  · exact (hmeas.norm.mul (Continuous.aestronglyMeasurable (by fun_prop))).restrict
  · rw [ae_restrict_iff' hset]
    filter_upwards with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound y hy

end GlobalTheory.HeckeTheta.Decay
