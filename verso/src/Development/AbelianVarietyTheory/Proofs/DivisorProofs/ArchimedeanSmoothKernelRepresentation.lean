import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MeasurableCompInfGL

noncomputable section

open Classical MeasureTheory NumberField Topology

namespace GlobalTheory.JSW

open GlobalTheory.CuspRep

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def unitOrOne (x : Lie E a) : GL (Fin a) (Cinf E) :=
  if h : IsUnit (Matrix.of x) then h.unit else 1

/- English proof (translation)
Distinguish the cases in `hx : x ∈ invSet E a`. Rewrite using `[Set.piecewise_eq_of_mem _ _ _ hx, unitOrOne, dif_pos (show IsUnit (Matrix.of x) from hx)]`. Both sides reduce to the same expression. Rewrite using `[Set.piecewise_eq_of_notMem _ _ _ hx, unitOrOne, dif_neg (show ¬ IsUnit (Matrix.of x) from hx)]`. Both sides reduce to the same expression.
-/
theorem unitOrOne_val (x : Lie E a) :
    (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E)) = (invSet E a).piecewise (fun y => Matrix.of y) (fun _ => 1) x := by
  by_cases hx : x ∈ invSet E a
  · rw [Set.piecewise_eq_of_mem _ _ _ hx, unitOrOne, dif_pos (show IsUnit (Matrix.of x) from hx)]; rfl
  · rw [Set.piecewise_eq_of_notMem _ _ _ hx, unitOrOne, dif_neg (show ¬ IsUnit (Matrix.of x) from hx)]; rfl

/- English proof (translation)
Establish `e : (fun x : Lie E a => (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E))) = (invSet E a).piecewise (fun y => Matrix.of y) (fun _ => 1)` using `funext unitOrOne_val`. Rewrite using `[e]`. Conclude with `Measurable.piecewise isOpen_invSet.measurableSet measurable_id measurable_const`.
-/
theorem measurable_unitOrOne : Measurable fun x : Lie E a => (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E)) := by
  have e : (fun x : Lie E a => (unitOrOne x : Matrix (Fin a) (Fin a) (Cinf E))) =
      (invSet E a).piecewise (fun y => Matrix.of y) (fun _ => 1) := funext unitOrOne_val
  rw [e]
  exact Measurable.piecewise isOpen_invSet.measurableSet measurable_id measurable_const

/- English proof (translation)
Establish `hev : (fun y : Lie E a => height (unitOrOne y)) =ᶠ[𝓝 x] fun y => 1 + ‖y‖ + ‖toL ((Matrix.of y)⁻¹)‖` using `by filter_upwards [isOpen_invSet.mem_nhds hx] with y hy`. Establish `h1 : ((unitOrOne y : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = Matrix.of y`. Rewrite using `[unitOrOne, dif_pos (show IsUnit (Matrix.of y) from hy)]`. Both sides reduce to the same expression. Establish `h2 : (((unitOrOne y)⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = (Matrix.of y)⁻¹`.

Rewrite using `[Matrix.coe_units_inv, h1]`. Simplify using `only [height, h1, h2]`. Both sides reduce to the same expression. Use `ContinuousAt.congr ?_ hev.symm` and prove the remaining obligations. Establish `hinv : ContinuousAt (fun y : Matrix (Fin a) (Fin a) (Cinf E) => y⁻¹) (Matrix.of x)`.

Use `continuousAt_matrix_inv _ ?_` and prove the remaining obligations. Establish `hu : IsUnit (Matrix.of x).det` using `(Matrix.isUnit_iff_isUnit_det _).1 hx`. Rewrite using `[← hu.unit_spec]`. Conclude with `NormedRing.inverse_continuousAt hu.unit`. Conclude with `(continuousAt_const.add continuousAt_id.norm).add (hinv.comp (f := fun y : Lie E a => Matrix.of y) continuousAt_id).norm`.
-/
theorem continuousAt_height_unitOrOne {x : Lie E a} (hx : x ∈ invSet E a) :
    ContinuousAt (fun y : Lie E a => height (unitOrOne y)) x := by
  have hev : (fun y : Lie E a => height (unitOrOne y)) =ᶠ[𝓝 x]
      fun y => 1 + ‖y‖ + ‖toL ((Matrix.of y)⁻¹)‖ := by
    filter_upwards [isOpen_invSet.mem_nhds hx] with y hy
    have h1 : ((unitOrOne y : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = Matrix.of y := by
      rw [unitOrOne, dif_pos (show IsUnit (Matrix.of y) from hy)]; rfl
    have h2 : (((unitOrOne y)⁻¹ : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E)) = (Matrix.of y)⁻¹ := by
      rw [Matrix.coe_units_inv, h1]
    simp only [height, h1, h2]
    rfl
  refine ContinuousAt.congr ?_ hev.symm
  have hinv : ContinuousAt (fun y : Matrix (Fin a) (Fin a) (Cinf E) => y⁻¹) (Matrix.of x) := by
    refine continuousAt_matrix_inv _ ?_
    have hu : IsUnit (Matrix.of x).det := (Matrix.isUnit_iff_isUnit_det _).1 hx
    rw [← hu.unit_spec]
    exact NormedRing.inverse_continuousAt hu.unit
  exact (continuousAt_const.add continuousAt_id.norm).add (hinv.comp (f := fun y : Lie E a => Matrix.of y)
    continuousAt_id).norm

/- English proof (translation)
Use `⟨hf.1.continuous.measurable, measurable_unitOrOne, fun N => ?_⟩` and prove the remaining obligations. Establish `hc : Continuous fun x => ‖f x‖ * height (unitOrOne x) ^ N`. Use `continuous_iff_continuousAt.2 fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ tsupport f`. Conclude with `hf.1.continuous.continuousAt.norm.mul ((continuousAt_height_unitOrOne (hf.2.2 hx)).pow N)`.

Use `(continuousAt_const (y := (0 : ℝ))).congr ?_ filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy` and prove the remaining obligations. Simplify using `[hy]`. Establish `hs : HasCompactSupport fun x => ‖f x‖ * height (unitOrOne x) ^ N` using `hf.2.1.norm.mul_right`. Conclude with `hc.integrable_of_hasCompactSupport hs`.
-/
theorem IsTestInf.isRapidInf {f : Lie E a → ℂ} (hf : IsTestInf f) :
    IsRapidInf (volume : Measure (Lie E a)) f unitOrOne := by
  refine ⟨hf.1.continuous.measurable, measurable_unitOrOne, fun N => ?_⟩
  have hc : Continuous fun x => ‖f x‖ * height (unitOrOne x) ^ N := by
    refine continuous_iff_continuousAt.2 fun x => ?_
    by_cases hx : x ∈ tsupport f
    · exact hf.1.continuous.continuousAt.norm.mul ((continuousAt_height_unitOrOne (hf.2.2 hx)).pow N)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]
  have hs : HasCompactSupport fun x => ‖f x‖ * height (unitOrOne x) ^ N :=
    hf.2.1.norm.mul_right
  exact hc.integrable_of_hasCompactSupport hs

/- English proof (translation)
Introduce `E _ _ _ a f hf`. Use `⟨hf.isRapidInf, fun F => funext fun g => ?_⟩` and prove the remaining obligations. Simplify using `only [smoothInf, kerInf]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Distinguish the cases in `hx : IsUnit (Matrix.of x)`. Rewrite using `[chart, dif_pos hx, dif_pos hx]`. Establish `h0 : f x = 0` using `image_eq_zero_of_notMem_tsupport fun h => hx (hf.2.2 h)`. Simplify using `[h0]`.
-/
theorem isRapidInf_and_smoothInf_eq_kerInf :
    ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (f : Lie E a → ℂ), IsTestInf f →
      IsRapidInf (volume : Measure (Lie E a)) f (fun x : Lie E a =>
        if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (Cinf E))) ∧
      ∀ F : GA E a → ℂ, smoothInf f F = kerInf (volume : Measure (Lie E a)) f (fun x : Lie E a =>
        if h : IsUnit (Matrix.of x) then h.unit else (1 : GL (Fin a) (Cinf E))) F := by
  intro E _ _ _ a f hf
  refine ⟨hf.isRapidInf, fun F => funext fun g => ?_⟩
  simp only [smoothInf, kerInf]
  congr 1
  funext x
  by_cases hx : IsUnit (Matrix.of x)
  · rw [chart, dif_pos hx, dif_pos hx]
  · have h0 : f x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hf.2.2 h)
    simp [h0]

end GlobalTheory.JSW
