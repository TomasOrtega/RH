import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivMultilinearDiagonalLeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGaussianConvolutionSeriesCoefficientLeIntegrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianConvolutionSeriesCoefficientDescFactoriaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianIteratedFDerivWeightedExpBoundedStatement
open MeasureTheory Filter Topology

namespace GlobalTheory.ConvSeries

/- English proof (translation)
Introduce `E _ _ _ _ _ b c hb hc h t ht k n`. Use `set δ : ℝ := min 1 (b / (6 * c)) with hδ`. Establish `hδ0 : 0 < δ` using `lt_min one_pos (by positivity)`. Establish `hδ1 : δ ≤ 1` using `min_le_left _ _`. Establish `hδ2 : δ ≤ b / (6 * c)` using `min_le_right _ _`.

Use `set θ : ℝ := 1 + δ with hθ`. Use `set α : ℝ := (2 * c + b) / (2 * (b + c)) with hα`. Establish `hθ1 : 1 ≤ θ` using `by linarith`. Establish `hθpos : 0 < θ` using `by linarith`. Establish `hα0 : 0 < α` using `by positivity`.

Establish `hα1 : α < 1` using `by rw [hα, div_lt_one (by positivity)]; linarith`. Establish `hθα : c * θ ^ 2 ≤ α * (b + c)`. Establish `e1 : α * (b + c) = c + b / 2` using `by rw [hα]; field_simp`. Establish `e2 : δ * (6 * c) ≤ b` using `by rwa [le_div_iff₀ (by positivity)] at hδ2`. Rewrite using `[e1, hθ]`.

Use the polynomial consequences of the given equalities and inequalities. Use `choose K hK using fun m => GlobalTheory.T.gaussian_iteratedFDeriv_weighted_exp_bounded E c α hc hα1 k m`. Use `set M : ℕ → ℝ := fun i => ∫ a, (2 * c * ‖a‖) ^ i * ‖h a‖ with hM`. Establish `hM0 : ∀ i, 0 ≤ M i` using `fun i => integral_nonneg fun a => by positivity`. Use `set B : ℝ := θ ^ n * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M (n - i) * K i with hB`.

Establish `hK0 : ∀ m, 0 ≤ K m` using `fun m => le_trans (by positivity) (hK m 0)`. Establish `hB0 : 0 ≤ B`. Use `mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)` and prove the remaining obligations. Conclude with `mul_nonneg (mul_nonneg (by positivity) (hM0 _)) (hK0 _)`. Establish `hbound : ∀ j, SchwartzMap.seminorm ℂ k n (t j) ≤ θ⁻¹ ^ j * B`.

Introduce `j`. Use `SchwartzMap.seminorm_le_bound ℂ k n (t j) (by positivity) fun y => ?_` and prove the remaining obligations. Use `set s : ℝ := (2 * c) ^ j / (j.factorial : ℝ) with hs`. Establish `hs0 : 0 ≤ s` using `by positivity`. Use `set f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ := ((s : ℝ) : ℂ) • GlobalTheory.ConvSeries.coef b c (⇑h) j with hf`.

Establish `hfun : (⇑(t j)) = fun y => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * f (fun _ => y)`. Use function extensionality and compare the values at `y`. Rewrite using `[ht, GlobalTheory.ConvSeries.term, hf, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_assoc]`. Establish `hG : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)))`. Use `Complex.contDiff_exp.comp ?_` and prove the remaining obligations.

Use `ContDiff.neg ?_` and prove the remaining obligations. Conclude with `Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_norm_sq ℝ))`. Establish `hP : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => f (fun _ => y))` using `f.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)`. Establish `hL` using `norm_iteratedFDeriv_mul_le hG hP y (n := n) (by exact_mod_cast le_top)`. Rewrite using `[hfun]`.

Establish `hfn : ‖f‖ ≤ s * ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j`. Rewrite using `[hf, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]`. Conclude with `mul_le_mul_of_nonneg_left (GlobalTheory.T.norm_gaussianConvolutionSeriesCoefficient_le_integral E b c hb.le hc.le h j) hs0`. Establish `hterm : ∀ i ∈ Finset.range (n + 1), ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ * ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖) ≤ θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M (n - i) * K i))`. Introduce `i hi`.

Establish `hi' : i ≤ n` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)`. Use `set m := n - i`. Establish `h1` using `GlobalTheory.T.norm_iteratedFDeriv_multilinear_diagonal_le E j f m y`. Establish `h3` using `GlobalTheory.T.gaussianConvolutionSeriesCoefficient_descFactorial_estimate E b c θ α hc hθ1 hα0 hθα h j m y`. Establish `hPm : ‖iteratedFDeriv ℝ m (fun y : E => f (fun _ => y)) y‖ ≤ θ⁻¹ ^ (j - m) * Real.exp (c * α * ‖y‖ ^ 2) * M m`.

Use `h1.trans (le_trans ?_ h3)` and prove the remaining obligations. Use `mul_le_mul_of_nonneg_left hfn (by positivity : (0:ℝ) ≤ (j.descFactorial m : ℝ))` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `hθj : θ⁻¹ ^ (j - m) ≤ θ⁻¹ ^ j * θ ^ n`. Establish `hinv : 0 < θ⁻¹` using `inv_pos.2 hθpos`.

Establish `hle : θ⁻¹ ^ (j - m + m) ≤ θ⁻¹ ^ j` using `pow_le_pow_of_le_one hinv.le (inv_le_one_of_one_le₀ hθ1) (by omega)`. Establish `e : θ⁻¹ ^ (j - m) = θ⁻¹ ^ (j - m + m) * θ ^ m`. Rewrite using `[pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hθpos.ne', one_pow, mul_one]`. Rewrite using `[e]`. Conclude with `mul_le_mul hle (pow_le_pow_right₀ hθ1 (by omega)) (by positivity) (by positivity)`.

Establish `hGk` using `hK i y`. Establish `hch : (0:ℝ) ≤ n.choose i` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hPm.trans (by gcongr)`. Use `_ = θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M m * (‖y‖ ^ k * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ * Real.exp (c * α * ‖y‖ ^ 2)))) := by ring`.

Use `_ ≤ θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M m * K i)) := by gcongr`. Combine the equalities or inequalities in the displayed calculation. Establish `hgeom : Summable fun j : ℕ => θ⁻¹ ^ j * B` using `(summable_geometric_of_lt_one (inv_nonneg.2 hθpos.le) (inv_lt_one_of_one_lt₀ (by linarith))).mul_right B`. Conclude with `Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) hbound hgeom`.
-/
theorem summable_seminorm_term : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (b c : ℝ), 0 < b → 0 < c → ∀ (h : SchwartzMap E ℂ)
    (t : ℕ → SchwartzMap E ℂ), (∀ j y, t j y = GlobalTheory.ConvSeries.term b c h j y) →
    ∀ (k n : ℕ), Summable (fun j => SchwartzMap.seminorm ℂ k n (t j)) := by
  intro E _ _ _ _ _ b c hb hc h t ht k n

  set δ : ℝ := min 1 (b / (6 * c)) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ b / (6 * c) := min_le_right _ _
  set θ : ℝ := 1 + δ with hθ
  set α : ℝ := (2 * c + b) / (2 * (b + c)) with hα
  have hθ1 : 1 ≤ θ := by linarith
  have hθpos : 0 < θ := by linarith
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one (by positivity)]; linarith
  have hθα : c * θ ^ 2 ≤ α * (b + c) := by
    have e1 : α * (b + c) = c + b / 2 := by rw [hα]; field_simp
    have e2 : δ * (6 * c) ≤ b := by rwa [le_div_iff₀ (by positivity)] at hδ2
    rw [e1, hθ]; nlinarith

  choose K hK using fun m => GlobalTheory.T.gaussian_iteratedFDeriv_weighted_exp_bounded E c α hc hα1 k m
  set M : ℕ → ℝ := fun i => ∫ a, (2 * c * ‖a‖) ^ i * ‖h a‖ with hM
  have hM0 : ∀ i, 0 ≤ M i := fun i => integral_nonneg fun a => by positivity
  set B : ℝ := θ ^ n * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * M (n - i) * K i with hB
  have hK0 : ∀ m, 0 ≤ K m := fun m => le_trans (by positivity) (hK m 0)
  have hB0 : 0 ≤ B := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => ?_)
    exact mul_nonneg (mul_nonneg (by positivity) (hM0 _)) (hK0 _)
  have hbound : ∀ j, SchwartzMap.seminorm ℂ k n (t j) ≤ θ⁻¹ ^ j * B := by
    intro j
    refine SchwartzMap.seminorm_le_bound ℂ k n (t j) (by positivity) fun y => ?_
    set s : ℝ := (2 * c) ^ j / (j.factorial : ℝ) with hs
    have hs0 : 0 ≤ s := by positivity
    set f : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℂ :=
      ((s : ℝ) : ℂ) • GlobalTheory.ConvSeries.coef b c (⇑h) j with hf
    have hfun : (⇑(t j)) = fun y => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * f (fun _ => y) := by
      funext y
      rw [ht, GlobalTheory.ConvSeries.term, hf, ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_assoc]
    have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) := by
      refine Complex.contDiff_exp.comp ?_
      refine ContDiff.neg ?_
      exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_norm_sq ℝ))
    have hP : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => f (fun _ => y)) :=
      f.contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)
    have hL := norm_iteratedFDeriv_mul_le hG hP y (n := n) (by exact_mod_cast le_top)
    rw [hfun]
    have hfn : ‖f‖ ≤ s * ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j := by
      rw [hf, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      exact mul_le_mul_of_nonneg_left (GlobalTheory.T.norm_gaussianConvolutionSeriesCoefficient_le_integral E b c hb.le hc.le h j) hs0
    have hterm : ∀ i ∈ Finset.range (n + 1),
        ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖) ≤
        θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M (n - i) * K i)) := by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      set m := n - i
      have h1 := GlobalTheory.T.norm_iteratedFDeriv_multilinear_diagonal_le E j f m y
      have h3 := GlobalTheory.T.gaussianConvolutionSeriesCoefficient_descFactorial_estimate E b c θ α hc hθ1 hα0 hθα h j m y
      have hPm : ‖iteratedFDeriv ℝ m (fun y : E => f (fun _ => y)) y‖ ≤
          θ⁻¹ ^ (j - m) * Real.exp (c * α * ‖y‖ ^ 2) * M m := by
        refine h1.trans (le_trans ?_ h3)
        have := mul_le_mul_of_nonneg_left hfn (by positivity : (0:ℝ) ≤ (j.descFactorial m : ℝ))
        calc (j.descFactorial m : ℝ) * ‖f‖ * ‖y‖ ^ (j - m)
            ≤ (j.descFactorial m : ℝ) * (s * ∫ a, ‖GlobalTheory.ConvSeries.wt b c (⇑h) a‖ * ‖a‖ ^ j) * ‖y‖ ^ (j - m) := by
              gcongr
          _ = _ := by rw [hs]; ring
      have hθj : θ⁻¹ ^ (j - m) ≤ θ⁻¹ ^ j * θ ^ n := by
        have hinv : 0 < θ⁻¹ := inv_pos.2 hθpos
        have hle : θ⁻¹ ^ (j - m + m) ≤ θ⁻¹ ^ j :=
          pow_le_pow_of_le_one hinv.le (inv_le_one_of_one_le₀ hθ1) (by omega)
        have e : θ⁻¹ ^ (j - m) = θ⁻¹ ^ (j - m + m) * θ ^ m := by
          rw [pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hθpos.ne', one_pow, mul_one]
        rw [e]
        exact mul_le_mul hle (pow_le_pow_right₀ hθ1 (by omega)) (by positivity) (by positivity)
      have hGk := hK i y
      have hch : (0:ℝ) ≤ n.choose i := by positivity
      calc ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ m (fun y : E => f (fun _ => y)) y‖)
          ≤ ‖y‖ ^ k * ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            (θ⁻¹ ^ j * θ ^ n * Real.exp (c * α * ‖y‖ ^ 2) * M m)) := by
            gcongr
            exact hPm.trans (by gcongr)
        _ = θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M m *
            (‖y‖ ^ k * ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
              Real.exp (c * α * ‖y‖ ^ 2)))) := by ring
        _ ≤ θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M m * K i)) := by
            gcongr
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) * f (fun _ => y)) y‖
        ≤ ‖y‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖ := by gcongr
      _ = ∑ i ∈ Finset.range (n + 1), ‖y‖ ^ k * ((n.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i (fun y : E => Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) y‖ *
            ‖iteratedFDeriv ℝ (n - i) (fun y : E => f (fun _ => y)) y‖) := Finset.mul_sum _ _ _
      _ ≤ ∑ i ∈ Finset.range (n + 1), θ⁻¹ ^ j * (θ ^ n * ((n.choose i : ℝ) * M (n - i) * K i)) :=
            Finset.sum_le_sum hterm
      _ = θ⁻¹ ^ j * B := by rw [← Finset.mul_sum, ← Finset.mul_sum]
  have hgeom : Summable fun j : ℕ => θ⁻¹ ^ j * B :=
    (summable_geometric_of_lt_one (inv_nonneg.2 hθpos.le) (inv_lt_one_of_one_lt₀ (by linarith))).mul_right B
  exact Summable.of_nonneg_of_le (fun j => apply_nonneg _ _) hbound hgeom

end GlobalTheory.ConvSeries
