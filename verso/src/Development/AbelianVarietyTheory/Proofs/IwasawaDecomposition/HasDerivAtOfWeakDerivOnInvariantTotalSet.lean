import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegBaseY

namespace GlobalTheory.Mem.Osc

/- English proof (translation)
Establish `hiso : ∀ t a b, inner ℂ (U t a) (U t b) = inner ℂ a b` using `fun t a b => (⟨(U t).toLinearMap, hn t⟩ : H →ₗᵢ[ℂ] H).inner_map_map a b`. Establish `hadj : ∀ t a y, inner ℂ (U t a) y = inner ℂ a (U (-t) y)`. Introduce `t a y`. Establish `: U t (U (-t) y) = y`. Use `congrArg (fun A : H →L[ℂ] H => A y) (hadd t (-t))` as an intermediate fact.

Simplify `this.symm` using `[h0]`. Rewrite using `[← hiso t a (U (-t) y), this]`. Establish `hI : ∀ t : ℝ, HasDerivAt (fun u : ℝ => ∫ s in (0:ℝ)..u, U s w) (U t w) t` using `fun t => ((hc w).integral_hasStrictDerivAt 0 t).hasDerivAt`. Establish `hall : ∀ y ∈ D, ∀ t : ℝ, HasDerivAt (fun u : ℝ => inner ℂ (U u x) y) (inner ℂ (U t w) y) t`. Introduce `y hy t`.

Establish `h1` using `hw _ (hinv (-t) y hy)`. Rewrite `h1` using `[← hadj]`. Establish `h2 : HasDerivAt (fun u : ℝ => inner ℂ (U u x) (U (-t) y)) (inner ℂ (U t w) y) (t - t)`. Simplify using `using h1`. Establish `h3` using `h2.comp_sub_const t t`.

Use `h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Establish `h4 : U u x = U t (U (u - t) x)`. Use `congrArg (fun A : H →L[ℂ] H => A x) (hadd t (u - t))` as an intermediate fact. Simplify using `using this`. Simplify using `only`.

Rewrite using `[← hadj, ← h4]`. Establish `hz : ∀ y ∈ D, ∀ t : ℝ, inner ℂ (U t x - x - ∫ s in (0:ℝ)..t, U s w) y = 0`. Introduce `y hy t`. Establish `hd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => inner ℂ (U u x) y - inner ℂ (∫ s in (0:ℝ)..u, U s w) y) (0:ℂ) u`. Introduce `u`.

Establish `h5` using `(hI u).inner ℂ (hasDerivAt_const u y)`. Establish `h6` using `(hall y hy u).sub h5`. Simplify using `only [inner_zero_right, zero_add, sub_self] at h6`. Conclude with `h6`. Establish `h7` using `is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0`.

Simplify using `only [h0, intervalIntegral.integral_same, inner_zero_left, sub_zero, one_apply_eq_self] at h7`. Rewrite using `[inner_sub_left, inner_sub_left, ← h7]`. Expand and normalize the polynomial expressions, which then agree. Establish `hF : ∀ t : ℝ, U t x = x + ∫ s in (0:ℝ)..t, U s w`. Introduce `t`.

Establish `h8 : U t x - x - ∫ s in (0:ℝ)..t, U s w = 0`. Use `hD.eq_zero_of_inner_left (𝕜 := ℂ) ?_` and prove the remaining obligations. Introduce `v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem y hy => exact hz y hy t`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => simp only [inner_add_right] at *`. Rewrite using `[ha, hb, add_zero]`. Consider the case `smul c a _ ha => simp only [inner_smul_right] at *`. Rewrite using `[ha, mul_zero]`.

Rewrite `h8` using `[sub_sub, sub_eq_zero]`. Conclude with `h8`. Establish `h9` using `(hI 0).const_add x`. Simplify using `only [h0, one_apply_eq_self] at h9`. Conclude with `h9.congr_of_eventuallyEq (Filter.Eventually.of_forall hF)`.
-/
theorem hasDerivAt_of_weak_on_invariant_total
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : ℝ → H →L[ℂ] H) (D : Set H) (x w : H) (h0 : U 0 = 1)
    (hadd : ∀ s t, U (s + t) = U s * U t) (hn : ∀ t y, ‖U t y‖ = ‖y‖)
    (hc : ∀ y, Continuous fun t => U t y) (hD : Dense (Submodule.span ℂ D : Set H))
    (hinv : ∀ t, ∀ y ∈ D, U t y ∈ D)
    (hw : ∀ y ∈ D, HasDerivAt (fun t : ℝ => inner ℂ (U t x) y) (inner ℂ w y) 0) :
    HasDerivAt (fun t : ℝ => U t x) w 0 := by
  have hiso : ∀ t a b, inner ℂ (U t a) (U t b) = inner ℂ a b := fun t a b =>
    (⟨(U t).toLinearMap, hn t⟩ : H →ₗᵢ[ℂ] H).inner_map_map a b
  have hadj : ∀ t a y, inner ℂ (U t a) y = inner ℂ a (U (-t) y) := by
    intro t a y
    have : U t (U (-t) y) = y := by
      have := congrArg (fun A : H →L[ℂ] H => A y) (hadd t (-t))
      simpa [h0] using this.symm
    rw [← hiso t a (U (-t) y), this]
  have hI : ∀ t : ℝ, HasDerivAt (fun u : ℝ => ∫ s in (0:ℝ)..u, U s w) (U t w) t := fun t =>
    ((hc w).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hall : ∀ y ∈ D, ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => inner ℂ (U u x) y) (inner ℂ (U t w) y) t := by
    intro y hy t
    have h1 := hw _ (hinv (-t) y hy)
    rw [← hadj] at h1
    have h2 : HasDerivAt (fun u : ℝ => inner ℂ (U u x) (U (-t) y)) (inner ℂ (U t w) y) (t - t) := by
      simpa using h1
    have h3 := h2.comp_sub_const t t
    refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    have h4 : U u x = U t (U (u - t) x) := by
      have := congrArg (fun A : H →L[ℂ] H => A x) (hadd t (u - t))
      simpa using this
    simp only
    rw [← hadj, ← h4]
  have hz : ∀ y ∈ D, ∀ t : ℝ, inner ℂ (U t x - x - ∫ s in (0:ℝ)..t, U s w) y = 0 := by
    intro y hy t
    have hd : ∀ u : ℝ, HasDerivAt
        (fun u : ℝ => inner ℂ (U u x) y - inner ℂ (∫ s in (0:ℝ)..u, U s w) y) (0:ℂ) u := by
      intro u
      have h5 := (hI u).inner ℂ (hasDerivAt_const u y)
      have h6 := (hall y hy u).sub h5
      simp only [inner_zero_right, zero_add, sub_self] at h6
      exact h6
    have h7 := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
      (fun u => (hd u).deriv) t 0
    simp only [h0, intervalIntegral.integral_same, inner_zero_left, sub_zero,
      one_apply_eq_self] at h7
    rw [inner_sub_left, inner_sub_left, ← h7]
    ring
  have hF : ∀ t : ℝ, U t x = x + ∫ s in (0:ℝ)..t, U s w := by
    intro t
    have h8 : U t x - x - ∫ s in (0:ℝ)..t, U s w = 0 := by
      refine hD.eq_zero_of_inner_left (𝕜 := ℂ) ?_
      intro v hv
      induction hv using Submodule.span_induction with
      | mem y hy => exact hz y hy t
      | zero => simp
      | add a b _ _ ha hb => simp only [inner_add_right] at *; rw [ha, hb, add_zero]
      | smul c a _ ha => simp only [inner_smul_right] at *; rw [ha, mul_zero]
    rw [sub_sub, sub_eq_zero] at h8
    exact h8
  have h9 := (hI 0).const_add x
  simp only [h0, one_apply_eq_self] at h9
  exact h9.congr_of_eventuallyEq (Filter.Eventually.of_forall hF)

end GlobalTheory.Mem.Osc
