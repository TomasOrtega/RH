import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLieCoord

noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.JSW

namespace GlobalTheory.JSW

/- English proof (translation)
Establish `h0 : 0 ≤ (a : ℝ) * (‖toL A‖ * ‖B‖)` using `by positivity`. Use `(pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_` and prove the remaining obligations. Use `show ‖(A * Matrix.of B) i j‖ ≤ _`. Rewrite using `[Matrix.mul_apply]`. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Establish `hk : ∀ k, ‖A i k * Matrix.of B k j‖ ≤ ‖toL A‖ * ‖B‖` using `fun k => by`. Use `(norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))` and prove the remaining obligations. Conclude with `(norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)`. Conclude with `(norm_le_pi_norm (B k) j).trans (norm_le_pi_norm B k)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_toL_mul_le {E : Type} [Field E] [NumberField E] {a : ℕ} (A : Matrix (Fin a) (Fin a) (Cinf E)) (B : Lie E a) :
    ‖toL (A * Matrix.of B)‖ ≤ a * (‖toL A‖ * ‖B‖) := by
  have h0 : 0 ≤ (a : ℝ) * (‖toL A‖ * ‖B‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  show ‖(A * Matrix.of B) i j‖ ≤ _
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have hk : ∀ k, ‖A i k * Matrix.of B k j‖ ≤ ‖toL A‖ * ‖B‖ := fun k => by
    refine (norm_mul_le _ _).trans (mul_le_mul ?_ ?_ (norm_nonneg _) (norm_nonneg _))
    · exact (norm_le_pi_norm (toL A i) k).trans (norm_le_pi_norm (toL A) i)
    · exact (norm_le_pi_norm (B k) j).trans (norm_le_pi_norm B k)
  calc ∑ k, ‖A i k * Matrix.of B k j‖ ≤ ∑ _k : Fin a, ‖toL A‖ * ‖B‖ := Finset.sum_le_sum fun k _ => hk k
    _ = _ := by simp

/- English proof (translation)
Introduce `E _ _ _ a φ hC`. Use `choose C hC using hC`. Use `set D : ℝ := ∑ i, max (C i) 0 * ‖lieCoord E a i‖ with hDdef`. Establish `hD : 0 ≤ D` using `Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (norm_nonneg _)`. Establish `hlie : ∀ (X : Lie E a) (h : GA E a), ‖lieD X φ.1 h‖ ≤ D * ‖X‖`.

Introduce `X h`. Establish `e : lieD X φ.1 h = ∑ i, ((lieBasis E a).coord i X) • lieD (lieBasis E a i) φ.1 h` using `by conv_lhs => rw [← sum_lieCoord X]`. Simplify using `only [lieD, map_sum, map_smul]`. Rewrite using `[e, hDdef, Finset.sum_mul]`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[norm_smul]`. Establish `h1 : ‖(lieBasis E a).coord i X‖ ≤ ‖lieCoord E a i‖ * ‖X‖`. Establish `: ‖lieCoord E a i X‖ = ‖(lieBasis E a).coord i X‖` using `by simp [lieCoord]`. Rewrite using `[← this]`. Conclude with `(lieCoord E a i).le_opNorm X`.

Establish `h2 : ‖lieD (lieBasis E a i) φ.1 h‖ ≤ max (C i) 0`. Use `hC i h` as an intermediate fact. Rewrite `this` using `[GlobalTheory.CuspRep.lie_apply]`. Conclude with `this.trans (le_max_left _ _)`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨a * D, fun g y => ?_⟩` and prove the remaining obligations. Use `ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun W => ?_` and prove the remaining obligations. Use `set X : Lie E a := toL ((y⁻¹).val * Matrix.of W) with hX`. Establish `e` using `chart_lieD φ.2 X g (val_mem_invSet y)`. Establish `eW : rmul X (toL y.val) = W`.

Express the relevant statement in the definitionally equal form `y.val * ((y⁻¹).val * Matrix.of W) = Matrix.of W`. Rewrite using `[← mul_assoc, Units.mul_inv, one_mul]`. Rewrite `e` using `[eW, chart_val]`. Rewrite using `[← e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_fderiv_chart_le : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    (∀ i, ∃ C : ℝ, ∀ g, ‖(lie E a (lieBasis E a i) φ).1 g‖ ≤ C) →
      ∃ C : ℝ, ∀ (g : GA E a) (y : GL (Fin a) (Cinf E)), ‖fderiv ℝ (chart φ.1 g) (toL y.val)‖ ≤ C * ‖toL (y⁻¹).val‖ := by
  intro E _ _ _ a φ hC
  choose C hC using hC
  set D : ℝ := ∑ i, max (C i) 0 * ‖lieCoord E a i‖ with hDdef
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (norm_nonneg _)
  have hlie : ∀ (X : Lie E a) (h : GA E a), ‖lieD X φ.1 h‖ ≤ D * ‖X‖ := by
    intro X h
    have e : lieD X φ.1 h = ∑ i, ((lieBasis E a).coord i X) • lieD (lieBasis E a i) φ.1 h := by
      conv_lhs => rw [← sum_lieCoord X]
      simp only [lieD, map_sum, map_smul]
    rw [e, hDdef, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul]
    have h1 : ‖(lieBasis E a).coord i X‖ ≤ ‖lieCoord E a i‖ * ‖X‖ := by
      have : ‖lieCoord E a i X‖ = ‖(lieBasis E a).coord i X‖ := by simp [lieCoord]
      rw [← this]; exact (lieCoord E a i).le_opNorm X
    have h2 : ‖lieD (lieBasis E a i) φ.1 h‖ ≤ max (C i) 0 := by
      have := hC i h
      rw [GlobalTheory.CuspRep.lie_apply] at this
      exact this.trans (le_max_left _ _)
    calc ‖(lieBasis E a).coord i X‖ * ‖lieD (lieBasis E a i) φ.1 h‖
        ≤ (‖lieCoord E a i‖ * ‖X‖) * max (C i) 0 := mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  refine ⟨a * D, fun g y => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun W => ?_
  set X : Lie E a := toL ((y⁻¹).val * Matrix.of W) with hX
  have e := chart_lieD φ.2 X g (val_mem_invSet y)
  have eW : rmul X (toL y.val) = W := by
    change y.val * ((y⁻¹).val * Matrix.of W) = Matrix.of W
    rw [← mul_assoc, Units.mul_inv, one_mul]
  rw [eW, chart_val] at e
  rw [← e]
  calc ‖lieD X φ.1 (g * infGL E a y)‖ ≤ D * ‖X‖ := hlie _ _
    _ ≤ D * (a * (‖toL (y⁻¹).val‖ * ‖W‖)) := mul_le_mul_of_nonneg_left (norm_toL_mul_le _ _) hD
    _ = a * D * ‖toL (y⁻¹).val‖ * ‖W‖ := by ring

end GlobalTheory.JSW
