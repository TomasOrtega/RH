import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLogLogCut
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffTube
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCutOffGradient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

/- English proof (translation)
Distinguish the cases in `h : (Function.support f).Finite`. Establish `hs : Function.support (fun i => |f i|) ⊆ ↑h.toFinset`. Introduce `i hi`. Simplify using `using hi`. Rewrite using `[finsum_eq_sum_of_support_subset (s := h.toFinset) f (by rw [Set.Finite.coe_toFinset]), finsum_eq_sum_of_support_subset _ hs]`.

Conclude with `Finset.abs_sum_le_sum_abs _ _`. Rewrite using `[finsum_of_infinite_support h, abs_zero]`. Conclude with `finsum_nonneg fun i => abs_nonneg _`.
-/
theorem abs_finsum_le_finsum_abs {α : Type*} (f : α → ℝ) : |∑ᶠ i, f i| ≤ ∑ᶠ i, |f i| := by
  by_cases h : (Function.support f).Finite
  · have hs : Function.support (fun i => |f i|) ⊆ ↑h.toFinset := by
      intro i hi
      simpa using hi
    rw [finsum_eq_sum_of_support_subset (s := h.toFinset) f (by rw [Set.Finite.coe_toFinset]),
      finsum_eq_sum_of_support_subset _ hs]
    exact Finset.abs_sum_le_sum_abs _ _
  · rw [finsum_of_infinite_support h, abs_zero]
    exact finsum_nonneg fun i => abs_nonneg _

variable {n d : ℕ}

/- English proof (translation)
The claim follows from `|chartDens J A f φ y| ≤ chartAbsDens J A f φ y := by classical refine (abs_finsum_le_finsum_abs _).trans (le_of_eq (finsum_congr fun x => ?_)) rw [finsum_eq_if, finsum_eq_if] split_ifs <;> simp`.
-/
theorem abs_chartDens_le (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    |chartDens J A f φ y| ≤ chartAbsDens J A f φ y := by
  classical
  refine (abs_finsum_le_finsum_abs _).trans (le_of_eq (finsum_congr fun x => ?_))
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs <;> simp

/- English proof (translation)
The claim follows from `finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity`.
-/
theorem chartAbsDens_nonneg (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    0 ≤ chartAbsDens J A f φ y :=
  finsum_nonneg fun _ => finsum_nonneg fun _ => by split_ifs <;> positivity

/- English proof (translation)
Take `⟨K, hK⟩` from `hG`. Introduce `n d J A P hJ hdim hA hP`. Establish `hA' : ContDiff ℝ ∞ fun x : Fin n → ℂ => A *ᵥ x` using `(LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).contDiff.restrict_scalars ℝ`. Establish `hc : Continuous fun x : Fin n → ℂ => ‖eval (A *ᵥ x) P‖ ^ 2` using `((MvPolynomial.continuous_eval P).comp hA'.continuous).norm.pow 2`. Establish `key : ∀ T : (Fin (d + 1) → ℂ) → ℝ, Integrable T → ∀ (k : ℕ) (F : (Fin (d + 1) → ℂ) → ℝ), (∀ y, ‖F y‖ ≤ K / ((k : ℝ) + 1) * T y) → ‖∫ y, F y‖ ≤ K / ((k : ℝ) + 1) * ∫ y, T y` using `fun T hTi k F hF => (norm_integral_le_of_norm_le (hTi.const_mul _) (Eventually.of_forall hF)).trans_eq (integral_const_mul _ _)`.

Establish `lim : ∀ c : ℝ, Tendsto (fun k : ℕ => K / ((k : ℝ) + 1) * c) atTop (𝓝 0)` using `fun c => by`. Establish `h` using `(tendsto_one_div_add_atTop_nhds_zero_nat.const_mul K).mul_const c`. Rewrite `h` using `[mul_zero, zero_mul]`. Conclude with `h.congr fun k => by ring`. Use `⟨logLogCutAlong A P, fun k => ((hS _ P).1 k).1.comp hA', fun k x => ((hS _ P).1 k).2.1 _, fun k => ⟨{x | ‖eval (A *ᵥ x) P‖ ^ 2 < cutLevel k}, isOpen_lt hc continuous_const, fun x hx => ?_, fun x hx => ((hS _ P).1 k).2.2 _ hx.1⟩, fun x _ hx => (hS _ P).2 _ hx, fun R => ?_, fun R φ …` and prove the remaining obligations.

Establish `hx0 : eval (A *ᵥ x) P = 0` using `hx show ‖eval (A *ᵥ x) P‖ ^ 2 < cutLevel k`. Rewrite using `[hx0, norm_zero, zero_pow two_ne_zero]`. Conclude with `(cutLevel_mem k).1`. Establish `hTi` using `hT n d J A P R (fun _ => euclPot) hJ hdim hA hP fun _ => smoothNear_of_contDiff (contDiff_euclPot n)`. Establish `hl` using `(lim (∫ y, tubeDens J A P R (fun _ => euclPot) y)).const_mul 2`.

Rewrite `hl` using `[mul_zero]`. Use `squeeze_zero_norm (fun k => ?_) hl` and prove the remaining obligations. Establish `h` using `hK n d J A P R (fun _ => euclPot) k`. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[two_mul]`.

Conclude with `add_le_add (key _ hTi k _ fun y => (abs_chartDens_le _ _ _ _ y).trans (h y hJ hdim hA).2.1) (key _ hTi k _ fun y => (abs_chartDens_le _ _ _ _ y).trans (h y hJ hdim hA).2.2)`. Use `squeeze_zero_norm (fun k => key _ (hT n d J A P R φ hJ hdim hA hP hφ) k _ fun y => ?_) (lim _)` and prove the remaining obligations. Rewrite using `[Real.norm_of_nonneg (chartAbsDens_nonneg _ _ _ _ y)]`. Conclude with `(hK n d J A P R φ k y hJ hdim hA).1`.
-/
theorem CutOff.proof (hS : CutOffShape.Statement) (hT : CutOffTube.Statement)
    (hG : CutOffGradient.Statement) : CutOff.Statement := by
  obtain ⟨K, hK⟩ := hG
  intro n d J A P hJ hdim hA hP
  have hA' : ContDiff ℝ ∞ fun x : Fin n → ℂ => A *ᵥ x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).contDiff.restrict_scalars ℝ
  have hc : Continuous fun x : Fin n → ℂ => ‖eval (A *ᵥ x) P‖ ^ 2 :=
    ((MvPolynomial.continuous_eval P).comp hA'.continuous).norm.pow 2
  have key : ∀ T : (Fin (d + 1) → ℂ) → ℝ, Integrable T → ∀ (k : ℕ) (F : (Fin (d + 1) → ℂ) → ℝ),
      (∀ y, ‖F y‖ ≤ K / ((k : ℝ) + 1) * T y) → ‖∫ y, F y‖ ≤ K / ((k : ℝ) + 1) * ∫ y, T y :=
    fun T hTi k F hF => (norm_integral_le_of_norm_le (hTi.const_mul _)
      (Eventually.of_forall hF)).trans_eq (integral_const_mul _ _)
  have lim : ∀ c : ℝ, Tendsto (fun k : ℕ => K / ((k : ℝ) + 1) * c) atTop (𝓝 0) := fun c => by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul K).mul_const c
    rw [mul_zero, zero_mul] at h
    exact h.congr fun k => by ring
  refine ⟨logLogCutAlong A P, fun k => ((hS _ P).1 k).1.comp hA', fun k x => ((hS _ P).1 k).2.1 _,
    fun k => ⟨{x | ‖eval (A *ᵥ x) P‖ ^ 2 < cutLevel k}, isOpen_lt hc continuous_const, fun x hx => ?_,
      fun x hx => ((hS _ P).1 k).2.2 _ hx.1⟩, fun x _ hx => (hS _ P).2 _ hx, fun R => ?_,
    fun R φ hφ => ?_⟩
  · have hx0 : eval (A *ᵥ x) P = 0 := hx
    show ‖eval (A *ᵥ x) P‖ ^ 2 < cutLevel k
    rw [hx0, norm_zero, zero_pow two_ne_zero]
    exact (cutLevel_mem k).1
  · have hTi := hT n d J A P R (fun _ => euclPot) hJ hdim hA hP
      fun _ => smoothNear_of_contDiff (contDiff_euclPot n)
    have hl := (lim (∫ y, tubeDens J A P R (fun _ => euclPot) y)).const_mul 2
    rw [mul_zero] at hl
    refine squeeze_zero_norm (fun k => ?_) hl
    have h := hK n d J A P R (fun _ => euclPot) k
    refine (norm_sub_le _ _).trans ?_
    rw [two_mul]
    exact add_le_add (key _ hTi k _ fun y => (abs_chartDens_le _ _ _ _ y).trans (h y hJ hdim hA).2.1)
      (key _ hTi k _ fun y => (abs_chartDens_le _ _ _ _ y).trans (h y hJ hdim hA).2.2)
  · refine squeeze_zero_norm (fun k => key _ (hT n d J A P R φ hJ hdim hA hP hφ) k _ fun y => ?_)
      (lim _)
    rw [Real.norm_of_nonneg (chartAbsDens_nonneg _ _ _ _ y)]
    exact (hK n d J A P R φ k y hJ hdim hA).1

end

end GroundTheory.Heights₂.Heights
