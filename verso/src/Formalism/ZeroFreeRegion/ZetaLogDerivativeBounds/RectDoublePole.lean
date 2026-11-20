import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Formalism.LFunctionBounds.LFunctionBoundsProofs.RectResidue

open Complex

noncomputable section

namespace Formalism.ZF

/- English proof (authored)
The rectangle integral here uses the same four oriented side integrals as the rectangle integral in the residue theorem, so the two expressions agree by definition.
-/
theorem rdp_rectInt_eq_fx (g : ℂ → ℂ) (x0 x1 y0 y1 : ℝ) :
    rectInt g x0 x1 y0 y1 = Formalism.FX.rectInt g x0 x1 y0 y1 := rfl

/- English proof (authored)
On each of the four sides, linearity of the interval integral splits the sum into its two integrable parts. Combine the side integrals with their original signs and orientation factors to obtain the sum of the two rectangle integrals.
-/
theorem rdp_rectInt_add (f1 f2 : ℂ → ℂ) (x0 x1 y0 y1 : ℝ)
    (hB1 : IntervalIntegrable (fun x : ℝ => f1 (x + y0 * I)) MeasureTheory.volume x0 x1)
    (hB2 : IntervalIntegrable (fun x : ℝ => f2 (x + y0 * I)) MeasureTheory.volume x0 x1)
    (hT1 : IntervalIntegrable (fun x : ℝ => f1 (x + y1 * I)) MeasureTheory.volume x0 x1)
    (hT2 : IntervalIntegrable (fun x : ℝ => f2 (x + y1 * I)) MeasureTheory.volume x0 x1)
    (hR1 : IntervalIntegrable (fun y : ℝ => f1 (x1 + y * I)) MeasureTheory.volume y0 y1)
    (hR2 : IntervalIntegrable (fun y : ℝ => f2 (x1 + y * I)) MeasureTheory.volume y0 y1)
    (hL1 : IntervalIntegrable (fun y : ℝ => f1 (x0 + y * I)) MeasureTheory.volume y0 y1)
    (hL2 : IntervalIntegrable (fun y : ℝ => f2 (x0 + y * I)) MeasureTheory.volume y0 y1) :
    rectInt (fun w => f1 w + f2 w) x0 x1 y0 y1 =
      rectInt f1 x0 x1 y0 y1 + rectInt f2 x0 x1 y0 y1 := by
  simp only [rectInt]
  rw [intervalIntegral.integral_add hB1 hB2, intervalIntegral.integral_add hT1 hT2,
    intervalIntegral.integral_add hR1 hR2, intervalIntegral.integral_add hL1 hL2]
  ring

/- English proof (authored)
Away from p, differentiating 1/(z − p) gives −1/(z − p)². Multiplication by −a turns this into a/(z − p)².
-/
theorem rdp_hasDerivAt_prim (a p w : ℂ) (hw : w ≠ p) :
    HasDerivAt (fun z => -a * (z - p)⁻¹) (a / (w - p) ^ 2) w := by
  have hwp : w - p ≠ 0 := sub_ne_zero.2 hw
  have h := (((hasDerivAt_id' w).sub_const p).inv hwp).const_mul (-a)
  convert h using 1
  all_goals first | rfl | ring | (field_simp; ring) | (simp; ring)

/- English proof (authored)
The horizontal line avoids p because its height differs from the imaginary part of p. Along the line, the derivative of the primitive −a/(z − p) with respect to the real coordinate is the integrand. This derivative is continuous, so the fundamental theorem of calculus gives the difference of endpoint values.
-/
theorem rdp_horiz (a p : ℂ) (y x0 x1 : ℝ) (hy : y ≠ p.im) :
    ∫ x in x0..x1, a / ((x : ℂ) + y * I - p) ^ 2 =
      (-a * ((x1 : ℂ) + y * I - p)⁻¹) - (-a * ((x0 : ℂ) + y * I - p)⁻¹) := by
  have hne : ∀ x : ℝ, (x : ℂ) + y * I ≠ p := by
    intro x h
    apply hy
    have := congrArg Complex.im h
    simpa using this
  have hder : ∀ x : ℝ, HasDerivAt (fun t : ℝ => -a * ((t : ℂ) + y * I - p)⁻¹)
      (a / ((x : ℂ) + y * I - p) ^ 2) x := by
    intro x
    have hh : HasDerivAt (fun t : ℝ => (t : ℂ) + y * I) 1 x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * I)
    have h2 := (rdp_hasDerivAt_prim a p ((x : ℂ) + y * I) (hne x)).comp x hh
    simpa [Function.comp_def] using h2
  have hcont : Continuous (fun x : ℝ => a / ((x : ℂ) + y * I - p) ^ 2) := by
    refine Continuous.div continuous_const (by fun_prop) (fun x => ?_)
    exact pow_ne_zero _ (sub_ne_zero.2 (hne x))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
    (hcont.intervalIntegrable _ _)

/- English proof (authored)
The vertical line avoids p because its real coordinate differs from the real part of p. The chain rule gives the derivative of −a/(z − p) along the line as i times the integrand. This function is continuous. Integrate the derivative and pull the constant i outside the integral.
-/
theorem rdp_vert (a p : ℂ) (x y0 y1 : ℝ) (hx : x ≠ p.re) :
    I * ∫ y in y0..y1, a / ((x : ℂ) + y * I - p) ^ 2 =
      (-a * ((x : ℂ) + y1 * I - p)⁻¹) - (-a * ((x : ℂ) + y0 * I - p)⁻¹) := by
  have hne : ∀ y : ℝ, (x : ℂ) + y * I ≠ p := by
    intro y h
    apply hx
    have := congrArg Complex.re h
    simpa using this
  have hder : ∀ y : ℝ, HasDerivAt (fun t : ℝ => -a * ((x : ℂ) + t * I - p)⁻¹)
      (I * (a / ((x : ℂ) + y * I - p) ^ 2)) y := by
    intro y
    have hh : HasDerivAt (fun t : ℝ => (x : ℂ) + t * I) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp).mul_const I).const_add (x : ℂ)
    have h2 := (rdp_hasDerivAt_prim a p ((x : ℂ) + y * I) (hne y)).comp y hh
    simp only [Function.comp_def] at h2
    exact h2.congr_deriv (mul_comm _ _)
  have hcont : Continuous (fun y : ℝ => I * (a / ((x : ℂ) + y * I - p) ^ 2)) := by
    refine continuous_const.mul (Continuous.div continuous_const (by fun_prop) (fun y => ?_))
    exact pow_ne_zero _ (sub_ne_zero.2 (hne y))
  rw [← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hder y)
    (hcont.intervalIntegrable _ _)

/- English proof (authored)
Each side avoids the interior point p. The horizontal and vertical integral formulas express all four oriented side integrals as endpoint differences of the same primitive. Each corner value occurs once with each sign, and the sum is zero.
-/
theorem rdp_rectInt_double (a p : ℂ) (x0 x1 y0 y1 : ℝ) (h1 : x0 < p.re) (h2 : p.re < x1)
    (h3 : y0 < p.im) (h4 : p.im < y1) :
    rectInt (fun w => a / (w - p) ^ 2) x0 x1 y0 y1 = 0 := by
  simp only [rectInt]
  rw [rdp_horiz a p y0 x0 x1 (ne_of_lt h3), rdp_horiz a p y1 x0 x1 (ne_of_gt h4),
    rdp_vert a p x1 y0 y1 (ne_of_gt h2), rdp_vert a p x0 y0 y1 (ne_of_lt h1)]
  ring

/- English proof (authored)
Along the compact parameter interval, the curve avoids p. Hence the double-pole term is continuous, and the function obtained by subtracting it from g is the sum of the continuous remainder and the continuous simple-pole term. Both functions are integrable on the interval.
-/
theorem rdp_seg (g G : ℂ → ℂ) (a b p : ℂ) (γ : ℝ → ℂ) (s t : ℝ) (hγ : Continuous γ)
    (hG : ContinuousOn (fun u => G (γ u)) (Set.uIcc s t)) (hP : ∀ u ∈ Set.uIcc s t, γ u ≠ p)
    (hg : ∀ w : ℂ, w ≠ p → g w = G w + a / (w - p) ^ 2 + b / (w - p)) :
    IntervalIntegrable (fun u => g (γ u) - a / (γ u - p) ^ 2) MeasureTheory.volume s t ∧
    IntervalIntegrable (fun u => a / (γ u - p) ^ 2) MeasureTheory.volume s t := by
  have hD : ContinuousOn (fun u => a / (γ u - p) ^ 2) (Set.uIcc s t) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) (fun u hu => ?_)
    exact pow_ne_zero _ (sub_ne_zero.2 (hP u hu))
  have hS : ContinuousOn (fun u => G (γ u) + b / (γ u - p)) (Set.uIcc s t) := by
    refine hG.add (ContinuousOn.div continuousOn_const (by fun_prop) (fun u hu => ?_))
    exact sub_ne_zero.2 (hP u hu)
  refine ⟨(hS.congr fun u hu => ?_).intervalIntegrable, hD.intervalIntegrable⟩
  rw [hg _ (hP u hu)]
  ring

/- English proof (authored)
Each side lies in the open set on which the remainder is holomorphic, and each avoids the interior pole. The double-pole term and the function left after subtracting it are therefore integrable on every side. By linearity and the primitive calculation, the double-pole term contributes zero. The remaining integrand has a single simple-pole term with coefficient b, so the rectangle residue formula gives 2πib.
-/
theorem rectangle_double_pole : RectDoublePole := by
  intro g G a b p x0 x1 y0 y1 h1 h2 h3 h4 hU hg
  obtain ⟨U, hUo, hRU, hGU⟩ := hU
  have hGc : ContinuousOn G U := hGU.continuousOn
  have hx01 : x0 ≤ x1 := by linarith
  have hy01 : y0 ≤ y1 := by linarith

  have hmem : ∀ x y : ℝ, x ∈ Set.uIcc x0 x1 → y ∈ Set.uIcc y0 y1 → (x : ℂ) + y * I ∈ U := by
    intro x y hx hy
    apply hRU
    rw [Complex.mem_reProdIm]
    simp [hx, hy]
  have hseg : ∀ (γ : ℝ → ℂ) (s t : ℝ), Continuous γ → (∀ u ∈ Set.uIcc s t, γ u ∈ U) →
      (∀ u ∈ Set.uIcc s t, γ u ≠ p) →
      IntervalIntegrable (fun u => g (γ u) - a / (γ u - p) ^ 2) MeasureTheory.volume s t ∧
      IntervalIntegrable (fun u => a / (γ u - p) ^ 2) MeasureTheory.volume s t := by
    intro γ s t hγ hγU hγp
    exact rdp_seg g G a b p γ s t hγ (hGc.comp hγ.continuousOn fun u hu => hγU u hu) hγp hg
  have hxl : x0 ∈ Set.uIcc x0 x1 := Set.left_mem_uIcc
  have hxr : x1 ∈ Set.uIcc x0 x1 := Set.right_mem_uIcc
  have hyl : y0 ∈ Set.uIcc y0 y1 := Set.left_mem_uIcc
  have hyr : y1 ∈ Set.uIcc y0 y1 := Set.right_mem_uIcc
  have hB := hseg (fun x : ℝ => (x : ℂ) + y0 * I) x0 x1 (by fun_prop)
    (fun u hu => hmem u y0 hu hyl)
    (fun u _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have hT := hseg (fun x : ℝ => (x : ℂ) + y1 * I) x0 x1 (by fun_prop)
    (fun u hu => hmem u y1 hu hyr)
    (fun u _ h => by have := congrArg Complex.im h; simp at this; linarith)
  have hR := hseg (fun y : ℝ => (x1 : ℂ) + y * I) y0 y1 (by fun_prop)
    (fun u hu => hmem x1 u hxr hu)
    (fun u _ h => by have := congrArg Complex.re h; simp at this; linarith)
  have hL := hseg (fun y : ℝ => (x0 : ℂ) + y * I) y0 y1 (by fun_prop)
    (fun u hu => hmem x0 u hxl hu)
    (fun u _ h => by have := congrArg Complex.re h; simp at this; linarith)
  have hsplit : g = fun w => (g w - a / (w - p) ^ 2) + a / (w - p) ^ 2 := by
    funext w; ring
  rw [hsplit, rdp_rectInt_add _ _ x0 x1 y0 y1 hB.1 hB.2 hT.1 hT.2 hR.1 hR.2 hL.1 hL.2,
    rdp_rectInt_double a p x0 x1 y0 y1 h1 h2 h3 h4, add_zero, rdp_rectInt_eq_fx]
  have hres := Formalism.FX.rectangle_residue (fun w => g w - a / (w - p) ^ 2) G {p} (fun _ => b)
    x0 x1 y0 y1 (by linarith) (by linarith) (by simp [h1, h2, h3, h4]) ⟨U, hUo, hRU, hGU⟩
    (by
      intro w hw
      have hwp : w ≠ p := by simpa using hw
      simp only [Finset.sum_singleton]
      rw [hg w hwp]
      ring)
  simpa using hres

end Formalism.ZF
