import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThShiftInt

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def uu (TT : ℝ) (α : ℂ → ℂ) (ζ : ℂ) : ℂ := Complex.exp (I * (th TT α (Complex.log ζ) : ℂ))

/- English proof (translation)
Introduce and unpack `rfl`. Simplify using `[An] at hζ`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ne_zero_of_An (hTT : 0 ≤ TT) {ζ : ℂ} (hζ : ζ ∈ An TT) : ζ ≠ 0 := by
  rintro rfl
  simp [An] at hζ
  linarith

def br (s : Bool) (ζ : ℂ) : ℂ := if s then Complex.log ζ else Complex.log (-ζ) + Real.pi * I

def brD (s : Bool) : Set ℂ := if s then Complex.slitPlane else {ζ | -ζ ∈ Complex.slitPlane}

/- English proof (translation)
Consider the cases of `s`. Simplify using `only [brD, Bool.false_eq_true, ↓reduceIte]`. Conclude with `Complex.isOpen_slitPlane.preimage continuous_neg`. Simplify using `only [brD, ↓reduceIte]`. Conclude with `Complex.isOpen_slitPlane`.
-/
theorem isOpen_brD (s : Bool) : IsOpen (brD s) := by
  cases s
  · simp only [brD, Bool.false_eq_true, ↓reduceIte]
    exact Complex.isOpen_slitPlane.preimage continuous_neg
  · simp only [brD, ↓reduceIte]
    exact Complex.isOpen_slitPlane

/- English proof (translation)
Consider the cases of `s`. Simplify using `only [br, Bool.false_eq_true, ↓reduceIte]`. Rewrite using `[Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hζ), Complex.exp_pi_mul_I]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [br, ↓reduceIte]`.

Conclude with `Complex.exp_log hζ`.
-/
theorem exp_br (s : Bool) {ζ : ℂ} (hζ : ζ ≠ 0) : Complex.exp (br s ζ) = ζ := by
  cases s
  · simp only [br, Bool.false_eq_true, ↓reduceIte]
    rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hζ), Complex.exp_pi_mul_I]
    ring
  · simp only [br, ↓reduceIte]
    exact Complex.exp_log hζ

/- English proof (translation)
Distinguish the cases in `h : ζ ∈ Complex.slitPlane`. Conclude with `⟨true, by simpa [brD] using h⟩`. Use `⟨false, ?_⟩` and prove the remaining obligations. Simplify using `only [brD, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq]`. Rewrite `h`, the goal using `[Complex.mem_slitPlane_iff]`.

Use `push_neg at h`. Use `left`. Break down `h with ⟨h1, h2⟩` into its components or cases. Establish `h3 : ζ.re ≠ 0` using `fun h0 => hζ (Complex.ext (by simpa using h0) (by simpa using h2))`. Establish `h4 : ζ.re < 0` using `lt_of_le_of_ne h1 h3`.

Simplify using `only [Complex.neg_re]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_br {ζ : ℂ} (hζ : ζ ≠ 0) : ∃ s, ζ ∈ brD s := by
  by_cases h : ζ ∈ Complex.slitPlane
  · exact ⟨true, by simpa [brD] using h⟩
  · refine ⟨false, ?_⟩
    simp only [brD, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq]
    rw [Complex.mem_slitPlane_iff] at h ⊢
    push_neg at h
    left
    rcases h with ⟨h1, h2⟩
    have h3 : ζ.re ≠ 0 := fun h0 => hζ (Complex.ext (by simpa using h0) (by simpa using h2))
    have h4 : ζ.re < 0 := lt_of_le_of_ne h1 h3
    simp only [Complex.neg_re]
    linarith

/- English proof (translation)
Consider the cases of `s`. Simplify using `only [brD, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq] at hs`. Establish `e1 : br false = fun z : ℂ => Complex.log (-z) + Real.pi * I`. Use function extensionality and compare the values at `z`. Simplify using `[br]`.

Establish `h1 : HasDerivAt (fun z : ℂ => Complex.log (-z)) ((-ζ)⁻¹ * (-1)) ζ` using `(Complex.hasDerivAt_log hs).comp ζ (hasDerivAt_neg ζ)`. Establish `h2` using `h1.add_const ((Real.pi : ℂ) * I)`. Establish `e2 : (-ζ)⁻¹ * (-1) = ζ⁻¹` using `by rw [inv_neg, neg_mul_neg, mul_one]`. Rewrite `h2` using `[e2]`. Rewrite using `[e1]`.

Conclude with `h2`. Simplify using `only [brD, ↓reduceIte] at hs`. Establish `e1 : br true = Complex.log`. Use function extensionality and compare the values at `z`. Simplify using `[br]`.

Rewrite using `[e1]`. Conclude with `Complex.hasDerivAt_log hs`.
-/
theorem hasDerivAt_br (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) : HasDerivAt (br s) ζ⁻¹ ζ := by
  cases s
  · simp only [brD, Bool.false_eq_true, ↓reduceIte, Set.mem_setOf_eq] at hs
    have e1 : br false = fun z : ℂ => Complex.log (-z) + Real.pi * I := by
      funext z
      simp [br]
    have h1 : HasDerivAt (fun z : ℂ => Complex.log (-z)) ((-ζ)⁻¹ * (-1)) ζ :=
      (Complex.hasDerivAt_log hs).comp ζ (hasDerivAt_neg ζ)
    have h2 := h1.add_const ((Real.pi : ℂ) * I)
    have e2 : (-ζ)⁻¹ * (-1) = ζ⁻¹ := by rw [inv_neg, neg_mul_neg, mul_one]
    rw [e2] at h2
    rw [e1]
    exact h2
  · simp only [brD, ↓reduceIte] at hs
    have e1 : br true = Complex.log := by
      funext z
      simp [br]
    rw [e1]
    exact Complex.hasDerivAt_log hs

/- English proof (translation)
Establish `hd : DifferentiableOn ℂ (br s) (brD s)` using `fun z hz => (hasDerivAt_br s hz).differentiableAt.differentiableWithinAt`. Conclude with `(hd.contDiffOn (isOpen_brD s)).contDiffAt ((isOpen_brD s).mem_nhds hs)`.
-/
theorem contDiffAt_br (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) : ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (br s) ζ := by
  have hd : DifferentiableOn ℂ (br s) (brD s) := fun z hz =>
    (hasDerivAt_br s hz).differentiableAt.differentiableWithinAt
  exact (hd.contDiffOn (isOpen_brD s)).contDiffAt ((isOpen_brD s).mem_nhds hs)

/- English proof (translation)
Use `show Complex.exp (br s ζ) ∈ An TT`. Rewrite using `[exp_br s (ne_zero_of_An hTT hζ)]`. Conclude with `hζ`.
-/
theorem br_mem_Hh (s : Bool) (hTT : 0 ≤ TT) {ζ : ℂ} (hζ : ζ ∈ An TT) : br s ζ ∈ Hh TT := by
  show Complex.exp (br s ζ) ∈ An TT
  rw [exp_br s (ne_zero_of_An hTT hζ)]
  exact hζ

/- English proof (translation)
Unfold `uu`. Establish `h0` using `ne_zero_of_An hTT hζ`. Conclude with `expI_th_eq hTT hα hcurv hhol (br_mem_Hh true hTT hζ) (br_mem_Hh s hTT hζ) (by rw [Complex.exp_log h0, exp_br s h0])`.
-/
theorem uu_eq_br (hTT : 0 ≤ TT) (hα : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α (An TT))
    (hcurv : ∀ ζ : ℂ, TT < Complex.normSq ζ → (wZb α ζ).re = 0)
    (hhol : ∃ n : ℤ, (circleIntegral α 0 (TT + 1)).im = Real.pi * n) (s : Bool) {ζ : ℂ} (hζ : ζ ∈ An TT) :
    uu TT α ζ = Complex.exp (I * (th TT α (br s ζ) : ℂ)) := by
  unfold uu
  have h0 := ne_zero_of_An hTT hζ
  exact expI_th_eq hTT hα hcurv hhol (br_mem_Hh true hTT hζ) (br_mem_Hh s hTT hζ)
    (by rw [Complex.exp_log h0, exp_br s h0])

/- English proof (translation)
Rewrite using `[uu, mul_comm]`. Conclude with `Complex.norm_exp_ofReal_mul_I _`.
-/
theorem norm_uu (ζ : ℂ) : ‖uu TT α ζ‖ = 1 := by
  rw [uu, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
