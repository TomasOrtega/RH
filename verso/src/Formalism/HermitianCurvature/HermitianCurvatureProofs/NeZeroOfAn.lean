import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThShiftInt

open Set Filter Topology Complex

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {TT : ℝ} {α : ℂ → ℂ}

def uu (TT : ℝ) (α : ℂ → ℂ) (ζ : ℂ) : ℂ := Complex.exp (I * (th TT α (Complex.log ζ) : ℂ))

/- English proof (translation)
Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ne_zero_of_An (hTT : 0 ≤ TT) {ζ : ℂ} (hζ : ζ ∈ An TT) : ζ ≠ 0 := by
  rintro rfl
  simp [An] at hζ
  linarith

def br (s : Bool) (ζ : ℂ) : ℂ := if s then Complex.log ζ else Complex.log (-ζ) + Real.pi * I

def brD (s : Bool) : Set ℂ := if s then Complex.slitPlane else {ζ | -ζ ∈ Complex.slitPlane}

/- English proof (translation)
Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem isOpen_brD (s : Bool) : IsOpen (brD s) := by
  cases s
  · simp only [brD, Bool.false_eq_true, ↓reduceIte]
    exact Complex.isOpen_slitPlane.preimage continuous_neg
  · simp only [brD, ↓reduceIte]
    exact Complex.isOpen_slitPlane

/- English proof (translation)
Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem exp_br (s : Bool) {ζ : ℂ} (hζ : ζ ≠ 0) : Complex.exp (br s ζ) = ζ := by
  cases s
  · simp only [br, Bool.false_eq_true, ↓reduceIte]
    rw [Complex.exp_add, Complex.exp_log (neg_ne_zero.mpr hζ), Complex.exp_pi_mul_I]
    ring
  · simp only [br, ↓reduceIte]
    exact Complex.exp_log hζ

/- English proof (translation)
Consider separately whether the proposition holds or fails. Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the hypotheses and the conclusion using the stated equalities.

Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Combine the linear equalities and inequalities to obtain the conclusion.

A detailed English derivation is pending.
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
Split into cases according to the possible forms of the given data. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem contDiffAt_br (s : Bool) {ζ : ℂ} (hs : ζ ∈ brD s) : ContDiffAt ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (br s) ζ := by
  have hd : DifferentiableOn ℂ (br s) (brD s) := fun z hz =>
    (hasDerivAt_br s hz).differentiableAt.differentiableWithinAt
  exact (hd.contDiffOn (isOpen_brD s)).contDiffAt ((isOpen_brD s).mem_nhds hs)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem br_mem_Hh (s : Bool) (hTT : 0 ≤ TT) {ζ : ℂ} (hζ : ζ ∈ An TT) : br s ζ ∈ Hh TT := by
  show Complex.exp (br s ζ) ∈ An TT
  rw [exp_br s (ne_zero_of_An hTT hζ)]
  exact hζ

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem norm_uu (ζ : ℂ) : ‖uu TT α ζ‖ = 1 := by
  rw [uu, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
