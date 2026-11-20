import Mathlib

open scoped Topology

namespace GlobalTheory

open MeasureTheory AddCircle in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem circle_hom_eq_zpow :
    ∀ f : Circle →* Circle, Continuous f → ∃ n : ℤ, ∀ z, f z = z ^ n := by
  intro f hf
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let g : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun x => (f (toCircle x) : ℂ),
      continuous_subtype_val.comp (hf.comp continuous_toCircle)⟩
  have hg : ∀ x, g x = (f (toCircle x) : ℂ) := fun _ => rfl
  have hex : ∃ n : ℤ, fourierCoeff g n ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have h0 : fourierCoeff g = fun _ => 0 := funext hcon
    have hs := has_pointwise_sum_fourier_series_of_summable (f := g)
      (by rw [h0]; exact summable_zero) 0
    simp only [hcon, zero_smul] at hs
    have := hs.unique hasSum_zero
    rw [hg] at this
    exact Circle.coe_ne_zero _ this
  obtain ⟨n, hn⟩ := hex
  refine ⟨n, fun z => ?_⟩
  obtain ⟨w, rfl⟩ : ∃ w : AddCircle (1 : ℝ), toCircle w = z := by
    obtain ⟨w, hw⟩ := (homeomorphCircle (T := 1) one_ne_zero).surjective z
    exact ⟨w, by rw [← homeomorphCircle_apply one_ne_zero, hw]⟩
  have key : fourierCoeff g n = (fourier (-n) w * g w) * fourierCoeff g n := by
    unfold fourierCoeff
    rw [← integral_const_mul]
    rw [← integral_add_left_eq_self (μ := haarAddCircle)
      (fun t : AddCircle (1 : ℝ) => fourier (-n) t • g t) w]
    congr 1
    ext t
    simp only [hg, fourier_apply, zsmul_add, toCircle_add, map_mul, Circle.coe_mul, smul_eq_mul]
    ring
  have h1 : fourier (-n) w * g w = 1 := by
    have := mul_right_cancel₀ hn (key.symm.trans (one_mul _).symm)
    exact this
  rw [hg, fourier_apply, toCircle_zsmul, ← Circle.coe_mul, ← Circle.coe_one] at h1
  have h2 : toCircle w ^ (-n) * f (toCircle w) = (1 : Circle) := Circle.ext h1
  rw [zpow_neg, inv_mul_eq_one] at h2
  exact h2.symm

end GlobalTheory
