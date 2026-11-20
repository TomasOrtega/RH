import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

/- English proof (translation)
Introduce `n e δ h W g hW hg hδ`. Use `set S : Set (EuclideanSpace ℂ (Fin n)) := {y | ‖y‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf y) q = 0} with hS`. Use `set ν : Measure (EuclideanSpace ℂ (Fin n)) := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) with hν`. Use `set D : ℝ := (ν {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal with hD`. Establish `hδ1 : 1 ≤ δ` using `h2 n (e + 1) δ W g (Nat.succ_pos e) hW hg hδ`.

Establish `hmass : (ν S).toReal / D = δ`. Establish `hm` using `h1 n e δ h W g hW hg hδ`. Unfold `coneIntegral at hm`. Rewrite `hm` using `[setIntegral_const, measureReal_def, smul_eq_mul, mul_one]`. Conclude with `hm`.

Establish `hfin : ν S ≠ ⊤`. Introduce `hinf`. Rewrite `hmass` using `[hinf, ENNReal.toReal_top, zero_div]`. Establish `: (δ : ℝ) ≠ 0` using `by exact_mod_cast (by omega : δ ≠ 0)`. Conclude with `this hmass.symm`.

Establish `: IsFiniteMeasure (ν.restrict S)` using `isFiniteMeasure_restrict.2 hfin`. Establish `hcone : ∀ φ : (Fin n → ℂ) → ℝ, coneIntegral h W e φ = (∫ y, φ (h.pointOf y) ∂(ν.restrict S)) / D` using `fun _ => rfl`. Establish `hzero : ν.restrict S {(0 : EuclideanSpace ℂ (Fin n))} = 0`. Use `nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le S _).trans_eq ?_)` and prove the remaining obligations. Establish `hd : (((2 * (e + 1) : ℕ) : ℝ)) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ)` using `by simp`.

Rewrite using `[hν, hd]`. Apply `hausdorffMeasure_of_dimH_lt` to reduce the goal to its premises. Rewrite using `[dimH_singleton]`. Conclude with `(by omega : 0 < 2 * (e + 1))` after adjusting the coercions. Establish `hae : ∀ᵐ y ∂(ν.restrict S), y ≠ 0`.

Rewrite using `[ae_iff]`. Simplify using `using hzero`. Establish `hF` using `h3 n h (ν.restrict S) (fun v y => fsLog h (nrmv h v) (h.pointOf y)) (-(harmonic (n - 1) : ℝ) / 2) ((harmonic (n - 1) : ℝ) / 2 * (volume (ballH h)).toReal) (h5 n h) (hae.mono fun y hy => by`. Take `⟨hi, habs, hmean⟩` from `h4 n h y hy`. Conclude with `⟨hi, habs.le, hmean⟩)`.

Take `⟨hFi, hFm⟩` from `hF`. Establish `hfun : (fun v => coneIntegral h W e (fsLog h (nrmv h v))) = fun v => (∫ y, fsLog h (nrmv h v) (h.pointOf y) ∂(ν.restrict S)) / D`. Use function extensionality and compare the values at `v`. Conclude with `hcone _`. Rewrite using `[hfun]`.

Use `⟨hFi.div_const D, ?_⟩` and prove the remaining obligations. Rewrite using `[setAverage_eq, integral_div, ← smul_div_assoc, ← setAverage_eq, hFm, Measure.restrict_apply_univ, mul_div_assoc, hmass]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem ConeAverage.proof (h1 : ConeIntegralMass.Statement) (h2 : ChowDegreePos.Statement)
    (h3 : ConeFubini.Statement) (h4 : FsLogAverage.Statement) (h5 : FsLogMeasurable.Statement) :
    ConeAverage.Statement := by
  intro n e δ h W g hW hg hδ
  set S : Set (EuclideanSpace ℂ (Fin n)) :=
    {y | ‖y‖ < 1 ∧ ∀ q ∈ W, eval (h.pointOf y) q = 0} with hS
  set ν : Measure (EuclideanSpace ℂ (Fin n)) := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) with hν
  set D : ℝ := (ν {y : EuclideanSpace ℂ (Fin n) | ‖y‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → y j = 0}).toReal
    with hD
  have hδ1 : 1 ≤ δ := h2 n (e + 1) δ W g (Nat.succ_pos e) hW hg hδ
  have hmass : (ν S).toReal / D = δ := by
    have hm := h1 n e δ h W g hW hg hδ
    unfold coneIntegral at hm
    rw [setIntegral_const, measureReal_def, smul_eq_mul, mul_one] at hm
    exact hm
  have hfin : ν S ≠ ⊤ := by
    intro hinf
    rw [hinf, ENNReal.toReal_top, zero_div] at hmass
    have : (δ : ℝ) ≠ 0 := by exact_mod_cast (by omega : δ ≠ 0)
    exact this hmass.symm
  have : IsFiniteMeasure (ν.restrict S) := isFiniteMeasure_restrict.2 hfin
  have hcone : ∀ φ : (Fin n → ℂ) → ℝ,
      coneIntegral h W e φ = (∫ y, φ (h.pointOf y) ∂(ν.restrict S)) / D := fun _ => rfl
  have hzero : ν.restrict S {(0 : EuclideanSpace ℂ (Fin n))} = 0 := by
    refine nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le S _).trans_eq ?_)
    have hd : (((2 * (e + 1) : ℕ) : ℝ)) = (((2 * (e + 1) : ℕ) : NNReal) : ℝ) := by simp
    rw [hν, hd]
    apply hausdorffMeasure_of_dimH_lt
    rw [dimH_singleton]
    exact_mod_cast (by omega : 0 < 2 * (e + 1))
  have hae : ∀ᵐ y ∂(ν.restrict S), y ≠ 0 := by
    rw [ae_iff]
    simpa using hzero
  have hF := h3 n h (ν.restrict S) (fun v y => fsLog h (nrmv h v) (h.pointOf y))
    (-(harmonic (n - 1) : ℝ) / 2)
    ((harmonic (n - 1) : ℝ) / 2 * (volume (ballH h)).toReal) (h5 n h)
    (hae.mono fun y hy => by
      obtain ⟨hi, habs, hmean⟩ := h4 n h y hy
      exact ⟨hi, habs.le, hmean⟩)
  obtain ⟨hFi, hFm⟩ := hF
  have hfun : (fun v => coneIntegral h W e (fsLog h (nrmv h v))) =
      fun v => (∫ y, fsLog h (nrmv h v) (h.pointOf y) ∂(ν.restrict S)) / D := by
    funext v
    exact hcone _
  rw [hfun]
  refine ⟨hFi.div_const D, ?_⟩
  rw [setAverage_eq, integral_div, ← smul_div_assoc, ← setAverage_eq, hFm,
    Measure.restrict_apply_univ, mul_div_assoc, hmass]
  ring

end

end GroundTheory.Heights₂.Heights
