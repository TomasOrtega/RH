import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelGramPosSemidef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareMetricPuncturedPolydiscBounds

set_option autoImplicit false

noncomputable section

open Complex Metric Matrix GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CurvInterp

/- English proof (translation)
Use `Complex.norm_deriv_le_div_of_mapsTo_ball hf (fun ζ hζ => ?_) hδ` and prove the remaining obligations. Rewrite using `[mem_closedBall, dist_eq_norm]`. Establish `h0` using `h1 0 (mem_ball_self hδ)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_deriv_le_of_norm_lt_one {f : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (ball 0 δ)) (h1 : ∀ ζ ∈ ball (0 : ℂ) δ, ‖f ζ‖ < 1) :
    ‖deriv f 0‖ ≤ 2 / δ := by
  refine Complex.norm_deriv_le_div_of_mapsTo_ball hf (fun ζ hζ => ?_) hδ
  rw [mem_closedBall, dist_eq_norm]
  have h0 := h1 0 (mem_ball_self hδ)
  calc ‖f ζ - f 0‖ ≤ ‖f ζ‖ + ‖f 0‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith [h1 ζ hζ]

/- English proof (translation)
Establish `hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball 0 δ)` using `(hf.deriv isOpen_ball).div hf hne`. Take `⟨g, hg0, hg⟩` from `hd.isExactOn_ball.with_val_at (0 : ℂ) 0`. Establish `h00 : (0 : ℂ) ∈ ball (0 : ℂ) δ` using `mem_ball_self hδ`. Establish `hf0 : f 0 ≠ 0` using `hne 0 h00`. Establish `hfd : ∀ z ∈ ball (0 : ℂ) δ, HasDerivAt f (deriv f z) z` using `fun z hz => ((hf z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt`.

Establish `hexp : ∀ z ∈ ball (0 : ℂ) δ, f z = f 0 * Complex.exp (g z)`. Introduce `z hz`. Establish `hh : ∀ z ∈ ball (0 : ℂ) δ, HasDerivAt (fun w => f w * Complex.exp (-g w)) 0 z`. Introduce `z hz`. Establish `h1 : HasDerivAt (fun w => f w * Complex.exp (-g w)) (deriv f z * Complex.exp (-g z) + f z * (Complex.exp (-g z) * -(deriv f z / f z))) z` using `(hfd z hz).mul ((hg z hz).neg.cexp)`.

Use `h1.congr_deriv ?_` and prove the remaining obligations. Establish `e : f z * (deriv f z / f z) = deriv f z` using `mul_div_cancel₀ _ (hne z hz)`. Take the linear combination `(-Complex.exp (-g z)) * e`. Establish `hconst` using `isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) δ).isPreconnected (fun z hz => (hh z hz).differentiableAt.differentiableWithinAt) (fun z hz => by simpa using (hh z hz).deriv) hz h00`. Simplify using `only [hg0, neg_zero, Complex.exp_zero, mul_one] at hconst`.

Rewrite using `[← hconst, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]`. Establish `hp : 0 < ‖f 0‖` using `norm_pos_iff.2 hf0`. Use `set A := -Real.log ‖f 0‖ with hAdef`. Establish `hA : 0 < A` using `neg_pos.2 (Real.log_neg hp (h1 0 h00))`. Establish `hre : Set.MapsTo g (ball 0 δ) {u | u.re ≤ A}`.

Introduce `u hu`. Establish `h2` using `h1 u hu`. Rewrite `h2` using `[hexp u hu, norm_mul, Complex.norm_exp]`. Establish `h3` using `Real.log_neg (by positivity) h2`. Rewrite `h3` using `[Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp]`.

Use `show (g u).re ≤ A`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hgd : DifferentiableOn ℂ g (ball 0 δ)` using `fun u hu => (hg u hu).differentiableAt.differentiableWithinAt`. Establish `hsph : ∀ u ∈ sphere (0 : ℂ) (δ / 2), ‖g u‖ ≤ 2 * A`. Introduce `u hu`.

Establish `hn : ‖u‖ = δ / 2` using `by simpa using hu`. Establish `hu' : u ∈ ball (0 : ℂ) δ` using `by rw [mem_ball_zero_iff, hn]; linarith`. Establish `hBC` using `Complex.borelCaratheodory_zero hA hgd hre hδ hu' hg0`. Rewrite `hBC` using `[hn]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hdc : DiffContOnCl ℂ g (ball 0 (δ / 2))` using `hgd.diffContOnCl_ball (closedBall_subset_ball (by linarith))`. Establish `hC` using `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < δ / 2) hdc hsph`. Rewrite `hC` using `[(hg 0 h00).deriv, norm_div]`. Rewrite `hC` using `[div_le_iff₀ hp]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_deriv_le_of_punctured {f : ℂ → ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hf : DifferentiableOn ℂ f (ball 0 δ)) (hne : ∀ ζ ∈ ball (0 : ℂ) δ, f ζ ≠ 0)
    (h1 : ∀ ζ ∈ ball (0 : ℂ) δ, ‖f ζ‖ < 1) :
    ‖deriv f 0‖ ≤ 4 * (-Real.log ‖f 0‖) * ‖f 0‖ / δ := by
  have hd : DifferentiableOn ℂ (fun z => deriv f z / f z) (ball 0 δ) :=
    (hf.deriv isOpen_ball).div hf hne
  obtain ⟨g, hg0, hg⟩ := hd.isExactOn_ball.with_val_at (0 : ℂ) 0
  have h00 : (0 : ℂ) ∈ ball (0 : ℂ) δ := mem_ball_self hδ
  have hf0 : f 0 ≠ 0 := hne 0 h00
  have hfd : ∀ z ∈ ball (0 : ℂ) δ, HasDerivAt f (deriv f z) z := fun z hz =>
    ((hf z hz).differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
  have hexp : ∀ z ∈ ball (0 : ℂ) δ, f z = f 0 * Complex.exp (g z) := by
    intro z hz
    have hh : ∀ z ∈ ball (0 : ℂ) δ, HasDerivAt (fun w => f w * Complex.exp (-g w)) 0 z := by
      intro z hz
      have h1 : HasDerivAt (fun w => f w * Complex.exp (-g w))
          (deriv f z * Complex.exp (-g z) + f z * (Complex.exp (-g z) * -(deriv f z / f z))) z :=
        (hfd z hz).mul ((hg z hz).neg.cexp)
      refine h1.congr_deriv ?_
      have e : f z * (deriv f z / f z) = deriv f z := mul_div_cancel₀ _ (hne z hz)
      linear_combination (-Complex.exp (-g z)) * e
    have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) δ).isPreconnected
      (fun z hz => (hh z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => by simpa using (hh z hz).deriv) hz h00
    simp only [hg0, neg_zero, Complex.exp_zero, mul_one] at hconst
    rw [← hconst, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  have hp : 0 < ‖f 0‖ := norm_pos_iff.2 hf0
  set A := -Real.log ‖f 0‖ with hAdef
  have hA : 0 < A := neg_pos.2 (Real.log_neg hp (h1 0 h00))
  have hre : Set.MapsTo g (ball 0 δ) {u | u.re ≤ A} := by
    intro u hu
    have h2 := h1 u hu
    rw [hexp u hu, norm_mul, Complex.norm_exp] at h2
    have h3 := Real.log_neg (by positivity) h2
    rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp] at h3
    show (g u).re ≤ A
    linarith
  have hgd : DifferentiableOn ℂ g (ball 0 δ) := fun u hu => (hg u hu).differentiableAt.differentiableWithinAt
  have hsph : ∀ u ∈ sphere (0 : ℂ) (δ / 2), ‖g u‖ ≤ 2 * A := by
    intro u hu
    have hn : ‖u‖ = δ / 2 := by simpa using hu
    have hu' : u ∈ ball (0 : ℂ) δ := by rw [mem_ball_zero_iff, hn]; linarith
    have hBC := Complex.borelCaratheodory_zero hA hgd hre hδ hu' hg0
    rw [hn] at hBC
    calc ‖g u‖ ≤ 2 * A * (δ / 2) / (δ - δ / 2) := hBC
      _ = 2 * A := by field_simp; ring
  have hdc : DiffContOnCl ℂ g (ball 0 (δ / 2)) :=
    hgd.diffContOnCl_ball (closedBall_subset_ball (by linarith))
  have hC := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < δ / 2) hdc hsph
  rw [(hg 0 h00).deriv, norm_div] at hC
  rw [div_le_iff₀ hp] at hC
  calc ‖deriv f 0‖ ≤ 2 * A / (δ / 2) * ‖f 0‖ := hC
    _ = 4 * A * ‖f 0‖ / δ := by field_simp; ring

end GlobalTheory.CurvInterp

namespace GlobalTheory.CurvInterp

/- English proof (translation)
Rewrite using `[gnorm_sq (modelGram_posSemidef σ z), form_modelGram σ z w, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.modelAt]`. Establish `hle` using `Finset.single_le_sum (s := Finset.univ) (a := j) (f := fun k => (modelGram σ z k k).re * ‖w k‖ ^ 2) (fun k _ => by`. Simplify using `only [modelGram, diagonal_apply_eq, ofReal_re]`. Apply the tactic sequence `split_ifs <;> positivity) (Finset.mem_univ j)`. Use `hle.trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))` and prove the remaining obligations.

Simplify using `only [modelGram, diagonal_apply_eq, ofReal_re]`. Apply the tactic sequence `split_ifs <;> ring`.
-/
theorem modelGram_term_le {e m : ℕ} (σ : Fin m → Option (Fin e)) (z w : Fin e → ℂ) (j : Fin e) :
    (modelGram σ z j j).re * ‖w j‖ ^ 2 ≤ gnorm (modelGram σ z) w ^ 2 := by
  rw [gnorm_sq (modelGram_posSemidef σ z), form_modelGram σ z w, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.modelAt]
  have hle := Finset.single_le_sum (s := Finset.univ) (a := j)
    (f := fun k => (modelGram σ z k k).re * ‖w k‖ ^ 2) (fun k _ => by
      simp only [modelGram, diagonal_apply_eq, ofReal_re]
      split_ifs <;> positivity) (Finset.mem_univ j)
  refine hle.trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
  simp only [modelGram, diagonal_apply_eq, ofReal_re]
  split_ifs <;> ring

end GlobalTheory.CurvInterp

namespace GlobalTheory.CurvInterp

open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.PoincareBounds

/- English proof (translation)
Introduce `e m n k hk σ ρ φ hρ hφd hφD hφP`. Use `set ρ₀ := min ρ 1 with hρ₀`. Establish `hρ₀pos : 0 < ρ₀` using `lt_min hρ one_pos`. Establish `hρ₀1 : ρ₀ ≤ 1` using `min_le_right _ _`. Establish `hρ₀ρ : ρ₀ ≤ ρ` using `min_le_left _ _`.

Use `set δ₀ := min Real.pi (ρ₀ / 2) with hδ₀`. Establish `hδ₀pos : 0 < δ₀` using `lt_min Real.pi_pos (by positivity)`. Establish `hδ₀pi : δ₀ ≤ Real.pi` using `min_le_left _ _`. Establish `hδ₀ρ : δ₀ ≤ ρ₀ / 2` using `min_le_right _ _`. Establish `hρ'ρ₀ : ρ₀ ^ 2 / 2 ≤ ρ₀ / 2` using `by nlinarith`.

Use `⟨ρ₀ ^ 2 / 2, (n + 1) * (8 * Real.pi / δ₀), by positivity, by linarith, ?_⟩` and prove the remaining obligations. Introduce `z hz w`. Establish `hzρ : ‖z‖ < ρ₀ ^ 2 / 2` using `mem_ball_zero_iff.1 hz.1`. Establish `hzj : ∀ j, ‖z j‖ < ρ₀ ^ 2 / 2` using `fun j => (norm_le_pi_norm z j).trans_lt hzρ`. Establish `hzj1 : ∀ j, ‖z j‖ < 1` using `fun j => by linarith [hzj j]`.

Use `set M := gnorm (modelGram σ z) w with hMdef`. Establish `hM0 : 0 ≤ M` using `gnorm_nonneg _ _`. Establish `hbr : ∀ j, (∃ i, σ i = some j) → z j ≠ 0` using `fun j ⟨i, hi⟩ => hz.2 i j hi`. Establish `hwb : ∀ j, (∃ i, σ i = some j) → ‖w j‖ ≤ M * (‖z j‖ * tlog (z j))`. Introduce `j hj`.

Establish `h` using `modelGram_term_le σ z w j`. Simplify using `only [modelGram, diagonal_apply_eq, ofReal_re, if_pos hj] at h`. Take `⟨hp, -⟩` from `norm_mul_tlog_lt (hbr j hj) (hzj1 j)`. Establish `e1 : ‖z j‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf (z j) ^ 2 = (‖z j‖ * tlog (z j)) ^ 2`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf, tlog]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h` using `[e1, one_div, inv_mul_eq_div, div_le_iff₀ (by positivity), ← mul_pow]`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h`. Establish `hwM : ∀ j, ‖w j‖ ≤ M`. Introduce `j`.

Distinguish the cases in `hj : ∃ i, σ i = some j`. Take `⟨hp, hl⟩` from `norm_mul_tlog_lt (hbr j hj) (hzj1 j)`. Use polynomial arithmetic with `[hwb j hj]`. Establish `h` using `modelGram_term_le σ z w j`. Simplify using `only [modelGram, diagonal_apply_eq, ofReal_re, if_neg hj, one_mul] at h`.

Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) hM0 two_ne_zero).1 h`. Break down `hM0.eq_or_lt with hM | hMpos` into its components or cases. Establish `hw : w = 0` using `funext fun j => norm_le_zero_iff.1 (by rw [hM]; exact hwM j)`. Substitute `hw` using the available equality. Simplify using `only [map_zero, gnorm_zero]`.

Conclude with `mul_nonneg (by positivity) hM0`. Use `set δ := δ₀ / M with hδdef`. Establish `hδ : 0 < δ` using `div_pos hδ₀pos hMpos`. Establish `hδM : δ * M = δ₀` using `div_mul_cancel₀ _ hMpos.ne'`. Set `γ : ℂ → Fin e → ℂ` to `fun ζ j => if ∃ i, σ i = some j then z j * Complex.exp (ζ * (w j / z j)) else z j + ζ * w j`.

Establish `hγ0 : γ 0 = z`. Apply the tactic sequence `funext j; by_cases hj : ∃ i, σ i = some j <;> simp [γ, hj]`. Establish `hγd : HasDerivAt γ w 0`. Use `hasDerivAt_pi.2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : ∃ i, σ i = some j`.

Simplify using `only [γ, if_pos hj]`. Establish `h : HasDerivAt (fun ζ : ℂ => z j * Complex.exp (ζ * (w j / z j))) (z j * (Complex.exp (0 * (w j / z j)) * (w j / z j))) 0` using `((hasDerivAt_mul_const (w j / z j)).cexp).const_mul (z j)`. Use `h.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[zero_mul, Complex.exp_zero, one_mul, mul_div_cancel₀ _ (hbr j hj)]`. Simplify using `only [γ, if_neg hj]`.

Conclude with `(hasDerivAt_mul_const (w j)).const_add (z j)`. Establish `hγdiff : Differentiable ℂ γ`. Use `differentiable_pi.2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `hj : ∃ i, σ i = some j`. Simplify using `only [γ, if_pos hj]`.

Use `fun_prop`. Simplify using `only [γ, if_neg hj]`. Use `fun_prop`. Establish `hγmem : ∀ ζ ∈ ball (0 : ℂ) δ, γ ζ ∈ punct σ ρ`. Introduce `ζ hζ`.

Establish `hζ' : ‖ζ‖ < δ` using `mem_ball_zero_iff.1 hζ`. Establish `hcoord : ∀ j, ‖γ ζ j‖ < ρ₀`. Introduce `j`. Distinguish the cases in `hj : ∃ i, σ i = some j`. Simplify using `only [γ, if_pos hj]`.

Establish `hz0` using `hbr j hj`. Establish `hzp : 0 < ‖z j‖` using `norm_pos_iff.2 hz0`. Establish `ht` using `tlog_pos hz0 (hzj1 j)`. Use `set x := (ζ * (w j / z j)).re with hx`. Establish `hx1 : x ≤ ‖ζ‖ * (‖w j‖ / ‖z j‖)`.

Rewrite using `[hx]; exact (re_le_norm _).trans (by rw [norm_mul, norm_div])`. Establish `hx2 : ‖ζ‖ * (‖w j‖ / ‖z j‖) ≤ ‖ζ‖ * (M * tlog (z j))` using `by gcongr`. Rewrite using `[div_le_iff₀ hzp]`. Use polynomial arithmetic with `[hwb j hj]`. Establish `hx3 : ‖ζ‖ * (M * tlog (z j)) < δ * (M * tlog (z j))` using `by gcongr`.

Establish `hx4 : δ * (M * tlog (z j)) ≤ Real.pi * tlog (z j)`. Rewrite using `[← mul_assoc, hδM]`. Use `gcongr`. Establish `hx5 : Real.pi * tlog (z j) = -Real.log ‖z j‖ / 2`. Simplify using `only [tlog]`.

Clear the denominators using the available nonvanishing facts. Establish `hxl : 2 * x < -Real.log ‖z j‖` using `by linarith`. Establish `he : Real.exp (2 * x) < ‖z j‖⁻¹`. Combine the equalities or inequalities in the displayed calculation. Establish `hsq : (‖z j‖ * Real.exp x) ^ 2 < ρ₀ ^ 2`.

Establish `e2 : Real.exp x ^ 2 = Real.exp (2 * x)`. Rewrite using `[← Real.exp_nat_mul]`. Evaluate the numerical expressions. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[norm_mul, Complex.norm_exp]`.

Conclude with `(pow_lt_pow_iff_left₀ (by positivity) hρ₀pos.le two_ne_zero).1 hsq`. Simplify using `only [γ, if_neg hj]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← norm_mul]`. Conclude with `norm_add_le _ _`.

Use `_ ≤ ‖z j‖ + δ * M := by gcongr`. Conclude with `hwM j`. Use `_ < ρ₀ := by rw [hδM]; linarith [hzj j]`. Use `⟨mem_ball_zero_iff.2 ((pi_norm_lt_iff (by linarith)).2 fun j => (hcoord j).trans_le hρ₀ρ), fun i j hi => ?_⟩` and prove the remaining obligations. Establish `hj : ∃ i', σ i' = some j` using `⟨i, hi⟩`.

Simplify using `only [γ, if_pos hj]`. Conclude with `mul_ne_zero (hbr j ⟨i, hi⟩) (Complex.exp_ne_zero _)`. Establish `hρ'ρ : ρ₀ ^ 2 / 2 ≤ ρ` using `by linarith`. Establish `hzB : z ∈ ball (0 : Fin e → ℂ) ρ` using `punct_mono σ hρ'ρ hz |>.1`. Establish `hzP : φ z ∈ punctured hk 1` using `hφP z (punct_mono σ hρ'ρ hz)`.

Establish `hφz : DifferentiableAt ℂ φ z` using `(hφd z hzB).differentiableAt (isOpen_ball.mem_nhds hzB)`. Establish `hcomp : HasDerivAt (fun ζ => φ (γ ζ)) (fderiv ℂ φ z w) 0`. Establish `h : HasFDerivAt φ (fderiv ℂ φ z) (γ 0)` using `by rw [hγ0]; exact hφz.hasFDerivAt`. Conclude with `h.comp_hasDerivAt 0 hγd`. Establish `hmaps : Set.MapsTo γ (ball 0 δ) (ball 0 ρ)` using `fun ζ hζ => (hγmem ζ hζ).1`.

Establish `hFd : ∀ i, DifferentiableOn ℂ (fun ζ => φ (γ ζ) i) (ball 0 δ)` using `fun i => differentiableOn_pi.1 (hφd.comp hγdiff.differentiableOn hmaps) i`. Establish `hF1 : ∀ i, ∀ ζ ∈ ball (0 : ℂ) δ, ‖φ (γ ζ) i‖ < 1` using `fun i ζ hζ => hφD _ (hmaps hζ) i`. Establish `hder : ∀ i, deriv (fun ζ => φ (γ ζ) i) 0 = fderiv ℂ φ z w i` using `fun i => (hasDerivAt_pi.1 hcomp i).deriv`. Establish `hF0 : ∀ i, φ (γ 0) i = φ z i` using `fun i => by rw [hγ0]`. Use `set v := fderiv ℂ φ z w with hv`.

Establish `hδinv : 1 / δ = M / δ₀` using `by rw [hδdef]; field_simp`. Use `set K := 8 * Real.pi / δ₀ * M with hK`. Establish `hK0 : 0 ≤ K` using `by positivity`. Establish `hvall : ∀ i, ‖v i‖ ≤ K`. Introduce `i`.

Establish `h` using `norm_deriv_le_of_norm_lt_one hδ (hFd i) (hF1 i)`. Rewrite `h` using `[hder i]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hK, mul_div_assoc', div_mul_eq_mul_div]`. Use `gcongr`.

Combine the linear relations using `[Real.pi_gt_three]`. Establish `hvbr : ∀ i : Fin n, i.val < k → ‖v i‖ ≤ K * (‖φ z i‖ * tlog (φ z i))`. Introduce `i hi`. Establish `hne : ∀ ζ ∈ ball (0 : ℂ) δ, φ (γ ζ) i ≠ 0` using `fun ζ hζ => (hφP _ (hγmem ζ hζ)).2 ⟨i.val, hi⟩`. Establish `h` using `norm_deriv_le_of_punctured hδ (hFd i) hne (hF1 i)`.

Rewrite `h` using `[hder i, hF0 i]`. Establish `hl : -Real.log ‖φ z i‖ = 2 * Real.pi * tlog (φ z i)`. Simplify using `only [tlog]`. Clear the denominators using the available nonvanishing facts. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hl, div_eq_mul_one_div, hδinv, hK]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hterm : ∀ i, pdiag k (φ z) i * ‖v i‖ ^ 2 ≤ K ^ 2`. Introduce `i`.

Unfold `pdiag`. Use `split_ifs with hi`. Establish `hp0 : φ z i ≠ 0` using `hzP.2 ⟨i.val, hi⟩`. Take `⟨hp, -⟩` from `norm_mul_tlog_lt hp0 (hzP.1 i)`. Establish `h` using `hvbr i hi`.

Establish `h2 : ‖v i‖ ^ 2 ≤ (K * (‖φ z i‖ * tlog (φ z i))) ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) h 2`. Establish `e1 : ‖φ z i‖ ^ 2 * tlog (φ z i) ^ 2 = (‖φ z i‖ * tlog (φ z i)) ^ 2` using `by ring`. Rewrite using `[e1, one_div_mul_eq_div, div_le_iff₀ (by positivity)]`. Use polynomial arithmetic with `[sq_nonneg K, sq_nonneg (‖φ z i‖ * tlog (φ z i))]`. Establish `h2 : ‖v i‖ ^ 2 ≤ K ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) (hvall i) 2`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hsum : gnorm (poincareGram k (φ z)) v ^ 2 ≤ ((n + 1) * K) ^ 2`. Rewrite using `[poincareGram_eq, gnorm_diag_sq _ (pdiag_nonneg k (φ z))]`. Combine the equalities or inequalities in the displayed calculation. Establish `: (n : ℝ) ≤ (n + 1) ^ 2` using `by nlinarith`.

Use polynomial arithmetic with `[sq_nonneg K]`. Establish `hfin` using `(pow_le_pow_iff_left₀ (gnorm_nonneg _ _) (by positivity) two_ne_zero).1 hsum`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem schwarz_punct : ∀ (e m n k : ℕ) (hk : k ≤ n) (σ : Fin m → Option (Fin e)) (ρ : ℝ)
    (φ : (Fin e → ℂ) → Fin n → ℂ), 0 < ρ → DifferentiableOn ℂ φ (Metric.ball 0 ρ) →
    (∀ z ∈ Metric.ball (0 : Fin e → ℂ) ρ, φ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1) →
    (∀ z ∈ punct σ ρ, φ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured hk 1) →
    ∃ ρ' C : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ z ∈ punct σ ρ', ∀ w,
      GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram k (φ z)) (fderiv ℂ φ z w) ≤
        C * GlobalTheory.HermFrame.gnorm (modelGram σ z) w := by
  intro e m n k hk σ ρ φ hρ hφd hφD hφP
  classical
  set ρ₀ := min ρ 1 with hρ₀
  have hρ₀pos : 0 < ρ₀ := lt_min hρ one_pos
  have hρ₀1 : ρ₀ ≤ 1 := min_le_right _ _
  have hρ₀ρ : ρ₀ ≤ ρ := min_le_left _ _
  set δ₀ := min Real.pi (ρ₀ / 2) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min Real.pi_pos (by positivity)
  have hδ₀pi : δ₀ ≤ Real.pi := min_le_left _ _
  have hδ₀ρ : δ₀ ≤ ρ₀ / 2 := min_le_right _ _
  have hρ'ρ₀ : ρ₀ ^ 2 / 2 ≤ ρ₀ / 2 := by nlinarith
  refine ⟨ρ₀ ^ 2 / 2, (n + 1) * (8 * Real.pi / δ₀), by positivity, by linarith, ?_⟩
  intro z hz w
  have hzρ : ‖z‖ < ρ₀ ^ 2 / 2 := mem_ball_zero_iff.1 hz.1
  have hzj : ∀ j, ‖z j‖ < ρ₀ ^ 2 / 2 := fun j => (norm_le_pi_norm z j).trans_lt hzρ
  have hzj1 : ∀ j, ‖z j‖ < 1 := fun j => by linarith [hzj j]
  set M := gnorm (modelGram σ z) w with hMdef
  have hM0 : 0 ≤ M := gnorm_nonneg _ _

  have hbr : ∀ j, (∃ i, σ i = some j) → z j ≠ 0 := fun j ⟨i, hi⟩ => hz.2 i j hi
  have hwb : ∀ j, (∃ i, σ i = some j) → ‖w j‖ ≤ M * (‖z j‖ * tlog (z j)) := by
    intro j hj
    have h := modelGram_term_le σ z w j
    simp only [modelGram, diagonal_apply_eq, ofReal_re, if_pos hj] at h
    obtain ⟨hp, -⟩ := norm_mul_tlog_lt (hbr j hj) (hzj1 j)
    have e1 : ‖z j‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf (z j) ^ 2 = (‖z j‖ * tlog (z j)) ^ 2 := by
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tOf, tlog]; ring
    rw [e1, one_div, inv_mul_eq_div, div_le_iff₀ (by positivity), ← mul_pow] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h
  have hwM : ∀ j, ‖w j‖ ≤ M := by
    intro j
    by_cases hj : ∃ i, σ i = some j
    · obtain ⟨hp, hl⟩ := norm_mul_tlog_lt (hbr j hj) (hzj1 j)
      nlinarith [hwb j hj]
    · have h := modelGram_term_le σ z w j
      simp only [modelGram, diagonal_apply_eq, ofReal_re, if_neg hj, one_mul] at h
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hM0 two_ne_zero).1 h
  rcases hM0.eq_or_lt with hM | hMpos
  · have hw : w = 0 := funext fun j => norm_le_zero_iff.1 (by rw [hM]; exact hwM j)
    subst hw
    simp only [map_zero, gnorm_zero]
    exact mul_nonneg (by positivity) hM0

  set δ := δ₀ / M with hδdef
  have hδ : 0 < δ := div_pos hδ₀pos hMpos
  have hδM : δ * M = δ₀ := div_mul_cancel₀ _ hMpos.ne'
  let γ : ℂ → Fin e → ℂ := fun ζ j =>
    if ∃ i, σ i = some j then z j * Complex.exp (ζ * (w j / z j)) else z j + ζ * w j
  have hγ0 : γ 0 = z := by
    funext j; by_cases hj : ∃ i, σ i = some j <;> simp [γ, hj]
  have hγd : HasDerivAt γ w 0 := by
    refine hasDerivAt_pi.2 fun j => ?_
    by_cases hj : ∃ i, σ i = some j
    · simp only [γ, if_pos hj]
      have h : HasDerivAt (fun ζ : ℂ => z j * Complex.exp (ζ * (w j / z j)))
          (z j * (Complex.exp (0 * (w j / z j)) * (w j / z j))) 0 :=
        ((hasDerivAt_mul_const (w j / z j)).cexp).const_mul (z j)
      refine h.congr_deriv ?_
      rw [zero_mul, Complex.exp_zero, one_mul, mul_div_cancel₀ _ (hbr j hj)]
    · simp only [γ, if_neg hj]
      exact (hasDerivAt_mul_const (w j)).const_add (z j)
  have hγdiff : Differentiable ℂ γ := by
    refine differentiable_pi.2 fun j => ?_
    by_cases hj : ∃ i, σ i = some j
    · simp only [γ, if_pos hj]; fun_prop
    · simp only [γ, if_neg hj]; fun_prop
  have hγmem : ∀ ζ ∈ ball (0 : ℂ) δ, γ ζ ∈ punct σ ρ := by
    intro ζ hζ
    have hζ' : ‖ζ‖ < δ := mem_ball_zero_iff.1 hζ
    have hcoord : ∀ j, ‖γ ζ j‖ < ρ₀ := by
      intro j
      by_cases hj : ∃ i, σ i = some j
      · simp only [γ, if_pos hj]
        have hz0 := hbr j hj
        have hzp : 0 < ‖z j‖ := norm_pos_iff.2 hz0
        have ht := tlog_pos hz0 (hzj1 j)
        set x := (ζ * (w j / z j)).re with hx
        have hx1 : x ≤ ‖ζ‖ * (‖w j‖ / ‖z j‖) := by
          rw [hx]; exact (re_le_norm _).trans (by rw [norm_mul, norm_div])
        have hx2 : ‖ζ‖ * (‖w j‖ / ‖z j‖) ≤ ‖ζ‖ * (M * tlog (z j)) := by
          gcongr
          rw [div_le_iff₀ hzp]; nlinarith [hwb j hj]
        have hx3 : ‖ζ‖ * (M * tlog (z j)) < δ * (M * tlog (z j)) := by
          gcongr
        have hx4 : δ * (M * tlog (z j)) ≤ Real.pi * tlog (z j) := by
          rw [← mul_assoc, hδM]; gcongr
        have hx5 : Real.pi * tlog (z j) = -Real.log ‖z j‖ / 2 := by
          simp only [tlog]; field_simp
        have hxl : 2 * x < -Real.log ‖z j‖ := by linarith
        have he : Real.exp (2 * x) < ‖z j‖⁻¹ := by
          calc Real.exp (2 * x) < Real.exp (-Real.log ‖z j‖) := Real.exp_lt_exp.2 hxl
            _ = ‖z j‖⁻¹ := by rw [Real.exp_neg, Real.exp_log hzp]
        have hsq : (‖z j‖ * Real.exp x) ^ 2 < ρ₀ ^ 2 := by
          have e2 : Real.exp x ^ 2 = Real.exp (2 * x) := by
            rw [← Real.exp_nat_mul]; norm_num
          calc (‖z j‖ * Real.exp x) ^ 2 = ‖z j‖ ^ 2 * Real.exp (2 * x) := by rw [mul_pow, e2]
            _ < ‖z j‖ ^ 2 * ‖z j‖⁻¹ := by gcongr
            _ = ‖z j‖ := by field_simp
            _ < ρ₀ ^ 2 := by nlinarith [hzj j]
        rw [norm_mul, Complex.norm_exp]
        exact (pow_lt_pow_iff_left₀ (by positivity) hρ₀pos.le two_ne_zero).1 hsq
      · simp only [γ, if_neg hj]
        calc ‖z j + ζ * w j‖ ≤ ‖z j‖ + ‖ζ‖ * ‖w j‖ := by
              rw [← norm_mul]; exact norm_add_le _ _
          _ ≤ ‖z j‖ + δ * M := by
              gcongr
              exact hwM j
          _ < ρ₀ := by rw [hδM]; linarith [hzj j]
    refine ⟨mem_ball_zero_iff.2 ((pi_norm_lt_iff (by linarith)).2 fun j => (hcoord j).trans_le hρ₀ρ),
      fun i j hi => ?_⟩
    have hj : ∃ i', σ i' = some j := ⟨i, hi⟩
    simp only [γ, if_pos hj]
    exact mul_ne_zero (hbr j ⟨i, hi⟩) (Complex.exp_ne_zero _)

  have hρ'ρ : ρ₀ ^ 2 / 2 ≤ ρ := by linarith
  have hzB : z ∈ ball (0 : Fin e → ℂ) ρ := punct_mono σ hρ'ρ hz |>.1
  have hzP : φ z ∈ punctured hk 1 := hφP z (punct_mono σ hρ'ρ hz)
  have hφz : DifferentiableAt ℂ φ z := (hφd z hzB).differentiableAt (isOpen_ball.mem_nhds hzB)
  have hcomp : HasDerivAt (fun ζ => φ (γ ζ)) (fderiv ℂ φ z w) 0 := by
    have h : HasFDerivAt φ (fderiv ℂ φ z) (γ 0) := by rw [hγ0]; exact hφz.hasFDerivAt
    exact h.comp_hasDerivAt 0 hγd
  have hmaps : Set.MapsTo γ (ball 0 δ) (ball 0 ρ) := fun ζ hζ => (hγmem ζ hζ).1
  have hFd : ∀ i, DifferentiableOn ℂ (fun ζ => φ (γ ζ) i) (ball 0 δ) := fun i =>
    differentiableOn_pi.1 (hφd.comp hγdiff.differentiableOn hmaps) i
  have hF1 : ∀ i, ∀ ζ ∈ ball (0 : ℂ) δ, ‖φ (γ ζ) i‖ < 1 := fun i ζ hζ => hφD _ (hmaps hζ) i
  have hder : ∀ i, deriv (fun ζ => φ (γ ζ) i) 0 = fderiv ℂ φ z w i := fun i =>
    (hasDerivAt_pi.1 hcomp i).deriv
  have hF0 : ∀ i, φ (γ 0) i = φ z i := fun i => by rw [hγ0]
  set v := fderiv ℂ φ z w with hv
  have hδinv : 1 / δ = M / δ₀ := by rw [hδdef]; field_simp
  set K := 8 * Real.pi / δ₀ * M with hK
  have hK0 : 0 ≤ K := by positivity
  have hvall : ∀ i, ‖v i‖ ≤ K := by
    intro i
    have h := norm_deriv_le_of_norm_lt_one hδ (hFd i) (hF1 i)
    rw [hder i] at h
    calc ‖v i‖ ≤ 2 / δ := h
      _ = 2 * (M / δ₀) := by rw [← hδinv]; ring
      _ ≤ K := by
        rw [hK, mul_div_assoc', div_mul_eq_mul_div]
        gcongr
        · linarith [Real.pi_gt_three]
  have hvbr : ∀ i : Fin n, i.val < k → ‖v i‖ ≤ K * (‖φ z i‖ * tlog (φ z i)) := by
    intro i hi
    have hne : ∀ ζ ∈ ball (0 : ℂ) δ, φ (γ ζ) i ≠ 0 := fun ζ hζ =>
      (hφP _ (hγmem ζ hζ)).2 ⟨i.val, hi⟩
    have h := norm_deriv_le_of_punctured hδ (hFd i) hne (hF1 i)
    rw [hder i, hF0 i] at h
    have hl : -Real.log ‖φ z i‖ = 2 * Real.pi * tlog (φ z i) := by
      simp only [tlog]; field_simp
    calc ‖v i‖ ≤ 4 * (-Real.log ‖φ z i‖) * ‖φ z i‖ / δ := h
      _ = K * (‖φ z i‖ * tlog (φ z i)) := by
        rw [hl, div_eq_mul_one_div, hδinv, hK]; field_simp; ring

  have hterm : ∀ i, pdiag k (φ z) i * ‖v i‖ ^ 2 ≤ K ^ 2 := by
    intro i
    unfold pdiag
    split_ifs with hi
    · have hp0 : φ z i ≠ 0 := hzP.2 ⟨i.val, hi⟩
      obtain ⟨hp, -⟩ := norm_mul_tlog_lt hp0 (hzP.1 i)
      have h := hvbr i hi
      have h2 : ‖v i‖ ^ 2 ≤ (K * (‖φ z i‖ * tlog (φ z i))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      have e1 : ‖φ z i‖ ^ 2 * tlog (φ z i) ^ 2 = (‖φ z i‖ * tlog (φ z i)) ^ 2 := by ring
      rw [e1, one_div_mul_eq_div, div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg K, sq_nonneg (‖φ z i‖ * tlog (φ z i))]
    · have h2 : ‖v i‖ ^ 2 ≤ K ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hvall i) 2
      nlinarith
  have hsum : gnorm (poincareGram k (φ z)) v ^ 2 ≤ ((n + 1) * K) ^ 2 := by
    rw [poincareGram_eq, gnorm_diag_sq _ (pdiag_nonneg k (φ z))]
    calc ∑ i, pdiag k (φ z) i * ‖v i‖ ^ 2 ≤ ∑ _i : Fin n, K ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = n * K ^ 2 := by simp
      _ ≤ ((n + 1) * K) ^ 2 := by
        have : (n : ℝ) ≤ (n + 1) ^ 2 := by nlinarith
        nlinarith [sq_nonneg K]
  have hfin := (pow_le_pow_iff_left₀ (gnorm_nonneg _ _) (by positivity) two_ne_zero).1 hsum
  calc gnorm (poincareGram k (φ z)) v ≤ (n + 1) * K := hfin
    _ = (n + 1) * (8 * Real.pi / δ₀) * M := by rw [hK]; ring

end GlobalTheory.CurvInterp
