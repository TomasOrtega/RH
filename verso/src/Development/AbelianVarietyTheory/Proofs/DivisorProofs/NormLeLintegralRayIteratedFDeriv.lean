import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLeLintegralTaylorTailIteratedDerivStatement
open MeasureTheory Filter Topology Set Module
open scoped ENNReal

namespace GlobalTheory

/- English proof (translation)
Use `set L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v with hL`. Establish `hLt : ∀ t : ℝ, L t = t • v` using `fun t => by simp [hL]`. Use `set Gx : E → F := fun z => G (x + z) with hGx`. Establish `hGx' : ContDiff ℝ (⊤ : ℕ∞) Gx` using `hG.comp (contDiff_const.add contDiff_id)`. Use `set h : ℝ → F := Gx ∘ L with hh`.

Establish `hhs : ContDiff ℝ (⊤ : ℕ∞) h` using `hGx'.comp L.contDiff`. Establish `key : ∀ (j : ℕ) (t : ℝ), iteratedDeriv j h t = iteratedFDeriv ℝ j G (x + t • v) (fun _ => v)`. Introduce `j t`. Rewrite using `[iteratedDeriv_eq_iteratedFDeriv, hh, L.iteratedFDeriv_comp_right hGx' t (by exact_mod_cast le_top), ContinuousMultilinearMap.compContinuousLinearMap_apply, hGx, iteratedFDeriv_comp_add_left, hLt]`. Simplify using `[hLt]`.

Establish `bound : ∀ (j : ℕ) (t : ℝ), ‖iteratedDeriv j h t‖ ≤ ‖iteratedFDeriv ℝ j G (x + t • v)‖ * ‖v‖ ^ j`. Introduce `j t`. Rewrite using `[key]`. Use `((iteratedFDeriv ℝ j G (x + t • v)).le_opNorm _).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `[Finset.prod_const]`.

Establish `hdec' : ∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0)`. Introduce `j hj`. Use `squeeze_zero_norm (fun t => bound j t) ?_` and prove the remaining obligations. Use `((hdec j hj).norm).mul_const (‖v‖ ^ j)` as an intermediate fact. Simplify using `using this`.

Establish `h0 : h 0 = G x` using `by simp [hh, hGx, hLt]`. Establish `main` using `GlobalTheory.T.norm_le_lintegral_taylor_tail_iteratedDeriv h m hhs hdec'`. Rewrite `main` using `[h0]`. Use `main.trans (lintegral_mono_ae ?_)` and prove the remaining obligations. Use `filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht`.

Establish `ha : 0 ≤ t ^ m / (m.factorial : ℝ)`. Establish `: (0:ℝ) < t` using `ht`. Check the signs of the components of the expression. Rewrite using `[← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul ha]`. Use `ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ ha)` and prove the remaining obligations.

Rewrite using `[mul_comm]`. Conclude with `bound (m + 1) t`.
-/
theorem norm_le_lintegral_ray_iteratedFDeriv
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (G : E → F) (m : ℕ) (x v : E)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hdec : ∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0)) :
    ENNReal.ofReal ‖G x‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
      (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by
  set L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v with hL
  have hLt : ∀ t : ℝ, L t = t • v := fun t => by simp [hL]
  set Gx : E → F := fun z => G (x + z) with hGx
  have hGx' : ContDiff ℝ (⊤ : ℕ∞) Gx := hG.comp (contDiff_const.add contDiff_id)
  set h : ℝ → F := Gx ∘ L with hh
  have hhs : ContDiff ℝ (⊤ : ℕ∞) h := hGx'.comp L.contDiff
  have key : ∀ (j : ℕ) (t : ℝ),
      iteratedDeriv j h t = iteratedFDeriv ℝ j G (x + t • v) (fun _ => v) := by
    intro j t
    rw [iteratedDeriv_eq_iteratedFDeriv, hh,
      L.iteratedFDeriv_comp_right hGx' t (by exact_mod_cast le_top),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, hGx,
      iteratedFDeriv_comp_add_left, hLt]
    simp [hLt]
  have bound : ∀ (j : ℕ) (t : ℝ),
      ‖iteratedDeriv j h t‖ ≤ ‖iteratedFDeriv ℝ j G (x + t • v)‖ * ‖v‖ ^ j := by
    intro j t
    rw [key]
    refine ((iteratedFDeriv ℝ j G (x + t • v)).le_opNorm _).trans (le_of_eq ?_)
    simp [Finset.prod_const]
  have hdec' : ∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0) := by
    intro j hj
    refine squeeze_zero_norm (fun t => bound j t) ?_
    have := ((hdec j hj).norm).mul_const (‖v‖ ^ j)
    simpa using this
  have h0 : h 0 = G x := by simp [hh, hGx, hLt]
  have main := GlobalTheory.T.norm_le_lintegral_taylor_tail_iteratedDeriv h m hhs hdec'
  rw [h0] at main
  refine main.trans (lintegral_mono_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ha : 0 ≤ t ^ m / (m.factorial : ℝ) := by
    have : (0:ℝ) < t := ht
    positivity
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul ha]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ ha)
  rw [mul_comm]
  exact bound (m + 1) t

end GlobalTheory
