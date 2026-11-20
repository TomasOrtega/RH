import Formalism.HermitianCurvature.HermitianCurvatureProofs.ImCircleIntegral

open Set Filter Topology Complex MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

/- English proof (translation)
Simplify using `only [Hh, Set.mem_ofPred_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]`.
-/
theorem Hh_add_int {w : ℂ} (k : ℤ) : w + (k : ℂ) * (2 * Real.pi * I) ∈ Hh TT ↔ w ∈ Hh TT := by
  simp only [Hh, Set.mem_ofPred_eq, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/- English proof (translation)
Use `(Hh_add_int (TT := TT) (w := w) 1).2 hw` as an intermediate fact. Simplify using `using this`.
-/
theorem Hh_add_one {w : ℂ} (hw : w ∈ Hh TT) : w + 2 * Real.pi * I ∈ Hh TT := by
  have := (Hh_add_int (TT := TT) (w := w) 1).2 hw
  simpa using this

/- English proof (translation)
Establish `hc : ∀ z ∈ Hh TT, HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I) - th TT α z) (0 : ℂ →L[ℝ] ℝ) z`. Introduce `z hz`. Establish `h1 : HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I)) (om α (z + 2 * Real.pi * I)) z`. Use `(hasFDerivAt_th hTT hα hcurv (Hh_add_one hz)).comp z ((hasFDerivAt_id z).add_const (2 * Real.pi * I))` as an intermediate fact. Conclude with `this`.

Establish `h2` using `hasFDerivAt_th hTT hα hcurv hz`. Establish `hom : om α (z + 2 * Real.pi * I) = om α z`. Use `bet_periodic α z 1` as an intermediate fact. Simplify using `only [Int.cast_one, one_mul] at this`. Simplify using `only [om, this]`.

Use `h1.sub h2` as an intermediate fact. Rewrite `this` using `[hom, sub_self]`. Then use the resulting hypothesis. Establish `hconst` using `(convex_Hh TT).is_const_of_fderivWithin_eq_zero (fun z hz => (hc z hz).differentiableAt.differentiableWithinAt) (fun z hz => (hc z hz).hasFDerivWithinAt.fderivWithin ((isOpen_Hh TT).uniqueDiffWithinAt hz)) (base_point_mem_half_plane hTT) hw`. Rewrite `hconst` using `[th_top hTT hα, theta_at_base_point_zero, sub_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem th_shift (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) {w : ℂ} (hw : w ∈ Hh TT) :
    th TT α (w + 2 * Real.pi * I) = th TT α w + 2 * (circleIntegral α 0 (TT + 1)).im := by
  have hc : ∀ z ∈ Hh TT, HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I) - th TT α z)
      (0 : ℂ →L[ℝ] ℝ) z := by
    intro z hz
    have h1 : HasFDerivAt (fun z => th TT α (z + 2 * Real.pi * I)) (om α (z + 2 * Real.pi * I)) z := by
      have := (hasFDerivAt_th hTT hα hcurv (Hh_add_one hz)).comp z
        ((hasFDerivAt_id z).add_const (2 * Real.pi * I))
      exact this
    have h2 := hasFDerivAt_th hTT hα hcurv hz
    have hom : om α (z + 2 * Real.pi * I) = om α z := by
      have := bet_periodic α z 1
      simp only [Int.cast_one, one_mul] at this
      simp only [om, this]
    have := h1.sub h2
    rwa [hom, sub_self] at this
  have hconst := (convex_Hh TT).is_const_of_fderivWithin_eq_zero
    (fun z hz => (hc z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hc z hz).hasFDerivWithinAt.fderivWithin ((isOpen_Hh TT).uniqueDiffWithinAt hz))
    (base_point_mem_half_plane hTT) hw
  rw [th_top hTT hα, theta_at_base_point_zero, sub_zero] at hconst
  linarith

/- English proof (translation)
Introduce `w hw`. Use `Int.induction_on k ?_ ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `n ih`. Establish `hmem : w + ((n : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT` using `(Hh_add_int (n : ℤ)).2 hw`.

Establish `h1` using `th_shift hTT hα hcurv hmem`. Move the coercions through the operations in `at ih h1 ⊢`. Rewrite using `[show w + ((n : ℂ) + 1) * (2 * Real.pi * I) = w + (n : ℂ) * (2 * Real.pi * I) + 2 * Real.pi * I by ring, h1, ih]`. Expand and normalize the polynomial expressions, which then agree. Introduce `n ih`.

Establish `hmem : w + ((-(n : ℤ) - 1 : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT` using `(Hh_add_int _).2 hw`. Establish `h1` using `th_shift hTT hα hcurv hmem`. Move the coercions through the operations in `at ih h1 ⊢`. Rewrite `h1` using `[show w + (-(n : ℂ) - 1) * (2 * Real.pi * I) + 2 * Real.pi * I = w + -(n : ℂ) * (2 * Real.pi * I) by ring, ih]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem th_shift_int (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0) (k : ℤ) :
    ∀ w ∈ Hh TT, th TT α (w + (k : ℂ) * (2 * Real.pi * I)) = th TT α w + k * (2 * (circleIntegral α 0 (TT + 1)).im) := by
  intro w hw
  refine Int.induction_on k ?_ ?_ ?_
  · simp
  · intro n ih
    have hmem : w + ((n : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT := (Hh_add_int (n : ℤ)).2 hw
    have h1 := th_shift hTT hα hcurv hmem
    push_cast at ih h1 ⊢
    rw [show w + ((n : ℂ) + 1) * (2 * Real.pi * I) = w + (n : ℂ) * (2 * Real.pi * I) + 2 * Real.pi * I by ring,
      h1, ih]
    ring
  · intro n ih
    have hmem : w + ((-(n : ℤ) - 1 : ℤ) : ℂ) * (2 * Real.pi * I) ∈ Hh TT := (Hh_add_int _).2 hw
    have h1 := th_shift hTT hα hcurv hmem
    push_cast at ih h1 ⊢
    rw [show w + (-(n : ℂ) - 1) * (2 * Real.pi * I) + 2 * Real.pi * I = w + -(n : ℂ) * (2 * Real.pi * I) by ring,
      ih] at h1
    linarith

/- English proof (translation)
Take `⟨n, hn⟩` from `Complex.exp_eq_exp_iff_exists_int.1 he`. Take `⟨m, hm⟩` from `hhol`. Establish `h` using `th_shift_int hTT hα hcurv n w' hw'`. Rewrite `h` using `[← hn, hm]`. Apply `Complex.exp_eq_exp_iff_exists_int.2` to reduce the goal to its premises.

Use `⟨n * m, ?_⟩` and prove the remaining obligations. Rewrite using `[h]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem expI_th_eq (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n)
    {w w' : ℂ} (hw : w ∈ Hh TT) (hw' : w' ∈ Hh TT) (he : Complex.exp w = Complex.exp w') :
    Complex.exp (I * (th TT α w : ℂ)) = Complex.exp (I * (th TT α w' : ℂ)) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.1 he
  obtain ⟨m, hm⟩ := hhol
  have h := th_shift_int hTT hα hcurv n w' hw'
  rw [← hn, hm] at h
  apply Complex.exp_eq_exp_iff_exists_int.2
  refine ⟨n * m, ?_⟩
  rw [h]
  push_cast
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
