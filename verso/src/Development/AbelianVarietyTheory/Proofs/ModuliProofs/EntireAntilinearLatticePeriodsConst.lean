import Mathlib

open Complex Matrix
open scoped ContDiff BigOperators Real

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Establish `hpos : 0 < ‖c‖` using `norm_pos_iff.mpr hc`. Establish `h0 : 0 ≤ C` using `(norm_nonneg _).trans (h 0)`. Establish `key` using `h ((C + 1) / ‖c‖)`. Rewrite `key` using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hpos.le), div_mul_cancel₀ _ hpos.ne']`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem eq_zero_of_norm_real_mul_le {c : ℂ} {C : ℝ} (h : ∀ r : ℝ, ‖(r : ℂ) * c‖ ≤ C) : c = 0 := by
  by_contra hc
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h0 : 0 ≤ C := (norm_nonneg _).trans (h 0)
  have key := h ((C + 1) / ‖c‖)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith) hpos.le), div_mul_cancel₀ _ hpos.ne'] at key
  linarith

/- English proof (translation)
Establish `hshift : ∀ a s, φ (s + a) - φ s = φ a - φ 0`. Introduce `a`. Establish `hd : Differentiable ℂ (fun s => φ (s + a) - φ s)` using `(hφ.comp (differentiable_id.add_const a)).sub hφ`. Establish `hbd : Bornology.IsBounded (Set.range (fun s => φ (s + a) - φ s))`. Rewrite using `[isBounded_iff_forall_norm_le]`.

Use `⟨2 * C + ‖(starRingEnd ℂ) a * b‖, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨s, rfl⟩`. Use `show ‖φ (s + a) - φ s‖ ≤ _`. Establish `e : φ (s + a) - φ s = ((φ (s + a) - (starRingEnd ℂ) (s + a) * b) - (φ s - (starRingEnd ℂ) s * b)) + (starRingEnd ℂ) a * b`. Rewrite using `[map_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Introduce `s`. Simplify `hd.apply_eq_apply_of_bounded hbd s 0` using `[zero_add]`.

Establish `hderiv : ∀ s, deriv φ s = deriv φ 0`. Introduce `s`. Establish `e1 : (fun x => φ (x + s)) = fun x => φ x + (φ s - φ 0)`. Use function extensionality and compare the values at `x`. Take the linear combination `hshift s x`.

Establish `e2` using `congrArg (fun f => deriv f 0) e1`. Simplify using `only [deriv_comp_add_const, deriv_add_const, zero_add] at e2`. Conclude with `e2`. Choose the witnesses or unpack the hypotheses as in `⟨β, hlin⟩ : ∃ β : ℂ, ∀ s, φ s = φ 0 + β * s := by`. Use `⟨deriv φ 0, fun s => ?_⟩` and prove the remaining obligations.

Establish `hd : Differentiable ℂ (fun s => φ s - deriv φ 0 * s)` using `hφ.sub (differentiable_id.const_mul _)`. Establish `hz : ∀ x, deriv (fun s => φ s - deriv φ 0 * s) x = 0`. Introduce `x`. Establish `hx : HasDerivAt (fun s => φ s - deriv φ 0 * s) (deriv φ x - deriv φ 0 * 1) x` using `(hφ x).hasDerivAt.sub ((hasDerivAt_id' x).const_mul _)`. Rewrite using `[hx.deriv, hderiv x]`.

Expand and normalize the polynomial expressions, which then agree. Use `is_const_of_deriv_eq_zero hd hz s 0` as an intermediate fact. Take the linear combination `this`. Establish `hB : ∀ s, ‖β * s - (starRingEnd ℂ) s * b‖ ≤ C + ‖φ 0‖`. Introduce `s`.

Establish `e : β * s - (starRingEnd ℂ) s * b = (φ s - (starRingEnd ℂ) s * b) - φ 0`. Rewrite using `[hlin s]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `(norm_sub_le _ _).trans (by linarith [h s])`.

Establish `h1 : β - b = 0` using `eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by`. Establish `hr` using `hB r`. Rewrite `hr` using `[Complex.conj_ofReal]`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : Complex.I * (β + b) = 0` using `eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by`.

Establish `hr` using `hB (r * Complex.I)`. Rewrite `hr` using `[map_mul, Complex.conj_ofReal, Complex.conj_I]`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : β + b = 0` using `(mul_eq_zero.mp h2).resolve_left Complex.I_ne_zero`. Establish `hβ : β = 0` using `by linear_combination (h1 + h3) / 2`.

Use `⟨by linear_combination (h3 - h1) / 2, fun s => ?_⟩` and prove the remaining obligations. Rewrite using `[hlin s, hβ, zero_mul, add_zero]`.
-/
theorem entire_sub_conj_bounded_const {φ : ℂ → ℂ} {b : ℂ} {C : ℝ} (hφ : Differentiable ℂ φ)
    (h : ∀ s, ‖φ s - (starRingEnd ℂ) s * b‖ ≤ C) : b = 0 ∧ ∀ s, φ s = φ 0 := by

  have hshift : ∀ a s, φ (s + a) - φ s = φ a - φ 0 := by
    intro a
    have hd : Differentiable ℂ (fun s => φ (s + a) - φ s) :=
      (hφ.comp (differentiable_id.add_const a)).sub hφ
    have hbd : Bornology.IsBounded (Set.range (fun s => φ (s + a) - φ s)) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨2 * C + ‖(starRingEnd ℂ) a * b‖, ?_⟩
      rintro _ ⟨s, rfl⟩
      show ‖φ (s + a) - φ s‖ ≤ _
      have e : φ (s + a) - φ s = ((φ (s + a) - (starRingEnd ℂ) (s + a) * b)
          - (φ s - (starRingEnd ℂ) s * b)) + (starRingEnd ℂ) a * b := by
        rw [map_add]; ring
      rw [e]
      calc _ ≤ ‖(φ (s + a) - (starRingEnd ℂ) (s + a) * b) - (φ s - (starRingEnd ℂ) s * b)‖
            + ‖(starRingEnd ℂ) a * b‖ := norm_add_le _ _
        _ ≤ (‖φ (s + a) - (starRingEnd ℂ) (s + a) * b‖ + ‖φ s - (starRingEnd ℂ) s * b‖)
            + ‖(starRingEnd ℂ) a * b‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ _ := by linarith [h (s + a), h s]
    intro s
    simpa [zero_add] using hd.apply_eq_apply_of_bounded hbd s 0

  have hderiv : ∀ s, deriv φ s = deriv φ 0 := by
    intro s
    have e1 : (fun x => φ (x + s)) = fun x => φ x + (φ s - φ 0) := by
      funext x
      linear_combination hshift s x
    have e2 := congrArg (fun f => deriv f 0) e1
    simp only [deriv_comp_add_const, deriv_add_const, zero_add] at e2
    exact e2

  obtain ⟨β, hlin⟩ : ∃ β : ℂ, ∀ s, φ s = φ 0 + β * s := by
    refine ⟨deriv φ 0, fun s => ?_⟩
    have hd : Differentiable ℂ (fun s => φ s - deriv φ 0 * s) :=
      hφ.sub (differentiable_id.const_mul _)
    have hz : ∀ x, deriv (fun s => φ s - deriv φ 0 * s) x = 0 := by
      intro x
      have hx : HasDerivAt (fun s => φ s - deriv φ 0 * s) (deriv φ x - deriv φ 0 * 1) x :=
        (hφ x).hasDerivAt.sub ((hasDerivAt_id' x).const_mul _)
      rw [hx.deriv, hderiv x]
      ring
    have := is_const_of_deriv_eq_zero hd hz s 0
    linear_combination this

  have hB : ∀ s, ‖β * s - (starRingEnd ℂ) s * b‖ ≤ C + ‖φ 0‖ := by
    intro s
    have e : β * s - (starRingEnd ℂ) s * b = (φ s - (starRingEnd ℂ) s * b) - φ 0 := by
      rw [hlin s]; ring
    rw [e]
    exact (norm_sub_le _ _).trans (by linarith [h s])
  have h1 : β - b = 0 := eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by
    have hr := hB r
    rw [Complex.conj_ofReal] at hr
    calc ‖(r : ℂ) * (β - b)‖ = ‖β * (r : ℂ) - (r : ℂ) * b‖ := by congr 1; ring
      _ ≤ _ := hr
  have h2 : Complex.I * (β + b) = 0 := eq_zero_of_norm_real_mul_le (C := C + ‖φ 0‖) fun r => by
    have hr := hB (r * Complex.I)
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I] at hr
    calc ‖(r : ℂ) * (Complex.I * (β + b))‖
        = ‖β * ((r : ℂ) * Complex.I) - (r : ℂ) * -Complex.I * b‖ := by congr 1; ring
      _ ≤ _ := hr
  have h3 : β + b = 0 := (mul_eq_zero.mp h2).resolve_left Complex.I_ne_zero
  have hβ : β = 0 := by linear_combination (h1 + h3) / 2
  refine ⟨by linear_combination (h3 - h1) / 2, fun s => ?_⟩
  rw [hlin s, hβ, zero_mul, add_zero]

/- English proof (translation)
Introduce `g Λ hdisc hspan v t hv hper`. Establish `: IsZLattice ℝ Λ` using `⟨hspan⟩`. Establish `hcont : Continuous (fun z => v z - t ⬝ᵥ star z)` using `hv.continuous.sub (continuous_const.dotProduct continuous_star)`. Establish `hperw : ∀ z w, w ∈ Λ → (fun z => v z - t ⬝ᵥ star z) (z + w) = (fun z => v z - t ⬝ᵥ star z) z`. Introduce `z w hw`.

Simplify using `only`. Rewrite using `[hper ⟨w, hw⟩ z, star_add, dotProduct_add]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨M, hM⟩` from `isBounded_iff_forall_norm_le.mp (IsZLattice.isCompact_range_of_periodic Λ _ hcont hperw).isBounded`. Establish `hline : ∀ d : Fin g → ℂ, t ⬝ᵥ star d = 0 ∧ ∀ s : ℂ, v (s • d) = v 0`.

Introduce `d`. Establish `hd : Differentiable ℂ (fun s : ℂ => v (s • d))` using `hv.comp (differentiable_id.smul_const d)`. Establish `hb : ∀ s : ℂ, ‖v (s • d) - (starRingEnd ℂ) s * (t ⬝ᵥ star d)‖ ≤ M`. Introduce `s`. Establish `e : (starRingEnd ℂ) s * (t ⬝ᵥ star d) = t ⬝ᵥ star (s • d)`.

Rewrite using `[star_smul, dotProduct_smul, smul_eq_mul, starRingEnd_apply]`. Rewrite using `[e]`. Conclude with `hM _ ⟨s • d, rfl⟩`. Take `⟨h1, h2⟩` from `entire_sub_conj_bounded_const hd hb`. Conclude with `⟨h1, fun s => by simpa using h2 s⟩`.

Use `⟨?_, fun z => by simpa using (hline z).2 1⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Establish `hi` using `(hline (Pi.single i 1)).1`. Rewrite `hi` using `[← Pi.single_star, star_one, dotProduct_single, mul_one]`. Simplify using `using hi`.
-/
theorem entire_antilinear_periods_const :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ →
      Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
      ∀ (v : (Fin g → ℂ) → ℂ) (t : (Fin g → ℂ)), Differentiable ℂ v →
        (∀ (l : Λ) z, v (z + l) = v z + t ⬝ᵥ star (l : (Fin g → ℂ))) →
        t = 0 ∧ ∀ z, v z = v 0 := by
  intro g Λ hdisc hspan v t hv hper
  have : IsZLattice ℝ Λ := ⟨hspan⟩

  have hcont : Continuous (fun z => v z - t ⬝ᵥ star z) :=
    hv.continuous.sub (continuous_const.dotProduct continuous_star)
  have hperw : ∀ z w, w ∈ Λ → (fun z => v z - t ⬝ᵥ star z) (z + w) = (fun z => v z - t ⬝ᵥ star z) z := by
    intro z w hw
    simp only
    rw [hper ⟨w, hw⟩ z, star_add, dotProduct_add]
    ring
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp
    (IsZLattice.isCompact_range_of_periodic Λ _ hcont hperw).isBounded

  have hline : ∀ d : Fin g → ℂ, t ⬝ᵥ star d = 0 ∧ ∀ s : ℂ, v (s • d) = v 0 := by
    intro d
    have hd : Differentiable ℂ (fun s : ℂ => v (s • d)) :=
      hv.comp (differentiable_id.smul_const d)
    have hb : ∀ s : ℂ, ‖v (s • d) - (starRingEnd ℂ) s * (t ⬝ᵥ star d)‖ ≤ M := by
      intro s
      have e : (starRingEnd ℂ) s * (t ⬝ᵥ star d) = t ⬝ᵥ star (s • d) := by
        rw [star_smul, dotProduct_smul, smul_eq_mul, starRingEnd_apply]
      rw [e]
      exact hM _ ⟨s • d, rfl⟩
    obtain ⟨h1, h2⟩ := entire_sub_conj_bounded_const hd hb
    exact ⟨h1, fun s => by simpa using h2 s⟩
  refine ⟨?_, fun z => by simpa using (hline z).2 1⟩
  funext i
  have hi := (hline (Pi.single i 1)).1
  rw [← Pi.single_star, star_one, dotProduct_single, mul_one] at hi
  simpa using hi

end GlobalTheory
