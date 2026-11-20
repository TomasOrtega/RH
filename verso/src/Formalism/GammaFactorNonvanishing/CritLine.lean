import Development.AutomorphicArithmetic.CharacterBoxes.EveryCharacter
import Formalism.GammaFactorNonvanishing.RhOfRight

open Complex DirichletCharacter

/- English proof (authored)
For an even character the factor is Γℝ(s), and for an odd character it is Γℝ(s + 1). Both arguments have positive real part. The real gamma factor is nonzero in that half-plane.
-/
theorem Formalism.VW.gammaFactor_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) : gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with h | h
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos hs
  · rw [h.gammaFactor_def]; exact Gammaℝ_ne_zero_of_re_pos (by rw [add_re, one_re]; linarith)

/- English proof (authored)
A zero strictly to the right of the critical line contradicts the assumed nonvanishing at once. Suppose it lies strictly to the left. The gamma factor at s is nonzero, so the completed L-function also vanishes there. The inverse character is primitive because inversion preserves its conductor. Its functional equation now gives a zero of the completed L-function at 1 − s.

Dividing by the gamma factor transfers that zero to the ordinary L-function of the inverse character. The point 1 − s has real part greater than 1/2 and is distinct from 1, so this again contradicts the assumed nonvanishing. The remaining possibility is Re(s) = 1/2.
-/
theorem Formalism.VW.critLine (h : UpperTheory.EveryCharacter) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (s : ℂ)
    (h0 : 0 < s.re) (h1 : s.re < 1) (hz : LFunction χ s = 0) : s.re = 1 / 2 := by
  have hs0 : s ≠ 0 := fun e => by simp [e] at h0
  have hs1 : s ≠ 1 := fun e => by simp [e] at h1
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hinv : χ⁻¹.IsPrimitive := by
      rw [isPrimitive_def, conductor_inv]; exact hχ
    have hc : completedLFunction χ s = 0 := by
      rw [LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)] at hz
      exact (div_eq_zero_iff.1 hz).resolve_right (Formalism.VW.gammaFactor_ne_zero χ h0)
    have hfe := hinv.completedLFunction_one_sub s
    rw [inv_inv, hc, mul_zero] at hfe
    have h2 : (1 - s) ≠ 0 := sub_ne_zero.2 hs1.symm
    refine h N χ⁻¹ (1 - s) (by rw [sub_re, one_re]; linarith) (Or.inr fun e => hs0 (by linear_combination -e)) ?_
    rw [LFunction_eq_completed_div_gammaFactor χ⁻¹ (1 - s) (Or.inl h2), hfe, zero_div]
  · exact h N χ s hgt (Or.inr hs1) hz

/- English proof (authored)
Take the trivial character of modulus 1, whose L-function equals the zeta function. The assumed nonvanishing for all characters therefore excludes zeta zeros with real part greater than 1/2 away from 1. The reduction for zeros of the zeta function now gives the Riemann Hypothesis.
-/
theorem Formalism.VW.rh_of_every (h : UpperTheory.EveryCharacter) : RiemannHypothesis :=
  Formalism.VW.rh_of_right fun s hs hs1 => by
    have := h 1 (1 : DirichletCharacter ℂ 1) s hs (Or.inr hs1)
    rwa [LFunction_modOne_eq] at this
