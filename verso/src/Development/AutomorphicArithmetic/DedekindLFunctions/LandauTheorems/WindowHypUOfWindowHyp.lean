import Development.AutomorphicArithmetic.DedekindLFunctions.LandauZeroFreeCriterion

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, ⟨h1, h2⟩, rfl⟩`. Conclude with `⟨Real.exp_le_exp.2 h1, Real.exp_le_exp.2 h2⟩`. Introduce and unpack `⟨h1, h2⟩`.

Establish `hy : 0 < y` using `lt_of_lt_of_le (Real.exp_pos a) h1`. Use `⟨Real.log y, ⟨?_, ?_⟩, Real.exp_log hy⟩` and prove the remaining obligations. Rewrite using `[← Real.exp_le_exp, Real.exp_log hy]`. Conclude with `h1`. Rewrite using `[← Real.exp_le_exp, Real.exp_log hy]`.

Conclude with `h2`.
-/
theorem windowHypU_of_windowHyp_image (a b : ℝ) :
    Real.exp '' Icc a b = Icc (Real.exp a) (Real.exp b) := by
  ext y
  constructor
  · rintro ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨Real.exp_le_exp.2 h1, Real.exp_le_exp.2 h2⟩
  · rintro ⟨h1, h2⟩
    have hy : 0 < y := lt_of_lt_of_le (Real.exp_pos a) h1
    refine ⟨Real.log y, ⟨?_, ?_⟩, Real.exp_log hy⟩
    · rw [← Real.exp_le_exp, Real.exp_log hy]; exact h1
    · rw [← Real.exp_le_exp, Real.exp_log hy]; exact h2

/- English proof (translation)
Use function extensionality and compare the values at `u`. Rewrite using `[abs_of_pos (Real.exp_pos u), smul_eq_mul, ← Real.exp_mul, mul_left_comm, ← Real.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem windowHypU_of_windowHyp_fun (R : ℝ → ℝ) (θ : ℝ) :
    (fun u : ℝ => |Real.exp u| • (R (Real.exp u) * Real.exp u ^ (-θ - 1))) =
      fun u => R (Real.exp u) * Real.exp (-θ * u) := by
  funext u
  rw [abs_of_pos (Real.exp_pos u), smul_eq_mul, ← Real.exp_mul, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

/- English proof (translation)
Introduce `η hη U₀`. Take `⟨Y, hY, R, hint, hR, hbound⟩` from `h η hη (Real.exp U₀)`. Establish `hYpos : 0 < Y` using `lt_of_lt_of_le (Real.exp_pos _) hY`. Establish `hS : Real.exp '' Icc (Real.log Y) ((1 + δ) * Real.log Y) = Icc Y (Y ^ (1 + δ))`. Rewrite using `[windowHypU_of_windowHyp_image, Real.exp_log hYpos, Real.rpow_def_of_pos hYpos, mul_comm]`.

Establish `hd : ∀ x ∈ Icc (Real.log Y) ((1 + δ) * Real.log Y), HasDerivWithinAt Real.exp (Real.exp x) (Icc (Real.log Y) ((1 + δ) * Real.log Y)) x` using `fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt`. Establish `hinj : InjOn Real.exp (Icc (Real.log Y) ((1 + δ) * Real.log Y))` using `Real.exp_injective.injOn`. Use `⟨Real.log Y, ?_, fun u => R (Real.exp u), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← Real.exp_le_exp, Real.exp_log hYpos]`. Conclude with `hY`.

Use `(integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hd hinj (fun y => R y * y ^ (-θ - 1))).1 (by rw [hS]; exact hint)` as an intermediate fact. Rewrite `this` using `[windowHypU_of_windowHyp_fun]`. Conclude with `this`. Introduce `u hu`. Establish `hmem : Real.exp u ∈ Icc Y (Y ^ (1 + δ))`.

Rewrite using `[← hS]`. Conclude with `⟨u, hu, rfl⟩`. Conclude with `hR _ hmem`. Establish `e` using `integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hd hinj (fun y => R y * y ^ (-θ - 1))`. Rewrite `e` using `[hS, windowHypU_of_windowHyp_fun]`.

Rewrite using `[← e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem windowHypU_of_windowHyp (F : CharFamily) {θ δ : ℝ} (hδ : 0 < δ) (h : WindowHyp F θ δ) :
    WindowHypU (gm F) θ δ := by
  intro η hη U₀
  obtain ⟨Y, hY, R, hint, hR, hbound⟩ := h η hη (Real.exp U₀)
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos _) hY
  have hS : Real.exp '' Icc (Real.log Y) ((1 + δ) * Real.log Y) = Icc Y (Y ^ (1 + δ)) := by
    rw [windowHypU_of_windowHyp_image, Real.exp_log hYpos, Real.rpow_def_of_pos hYpos, mul_comm]
  have hd : ∀ x ∈ Icc (Real.log Y) ((1 + δ) * Real.log Y),
      HasDerivWithinAt Real.exp (Real.exp x) (Icc (Real.log Y) ((1 + δ) * Real.log Y)) x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp (Icc (Real.log Y) ((1 + δ) * Real.log Y)) :=
    Real.exp_injective.injOn
  refine ⟨Real.log Y, ?_, fun u => R (Real.exp u), ?_, ?_, ?_⟩
  · rw [← Real.exp_le_exp, Real.exp_log hYpos]; exact hY
  · have := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Icc hd hinj
      (fun y => R y * y ^ (-θ - 1))).1 (by rw [hS]; exact hint)
    rw [windowHypU_of_windowHyp_fun] at this
    exact this
  · intro u hu
    have hmem : Real.exp u ∈ Icc Y (Y ^ (1 + δ)) := by
      rw [← hS]; exact ⟨u, hu, rfl⟩
    exact hR _ hmem
  · have e := integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hd hinj
      (fun y => R y * y ^ (-θ - 1))
    rw [hS, windowHypU_of_windowHyp_fun] at e
    rw [← e]
    calc ∫ y in Icc Y (Y ^ (1 + δ)), R y * y ^ (-θ - 1) ≤ Y ^ η := hbound
      _ = Real.exp (η * Real.log Y) := by rw [Real.rpow_def_of_pos hYpos, mul_comm]

end Deduction

end
