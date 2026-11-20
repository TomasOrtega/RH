import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference

open scoped NNReal

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

/- English proof (translation)
Establish `hwd : ((w d : ℝ≥0) : ℝ) ≠ 0`. Conclude with `(w.ne_zero_iff.2 hd)` after adjusting the coercions. Establish `hwc : ((w c : ℝ≥0) : ℝ) ≠ 0`. Conclude with `(w.ne_zero_iff.2 hc)` after adjusting the coercions. Establish `hl : Real.log ((w ℓ : ℝ≥0) : ℝ) ≠ 0`.

Use `(Real.log_neg ?_ ?_).ne` and prove the remaining obligations. Conclude with `h0` after adjusting the coercions. Conclude with `h1` after adjusting the coercions. Unfold `addVal`. Rewrite using `[map_mul, map_pow, map_inv₀]`.

Use `push_cast`. Rewrite using `[Real.log_mul (pow_ne_zero _ (inv_ne_zero hwd)) hwc, Real.log_pow, Real.log_inv]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem addVal_inv_pow_mul {C : Type} [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) {d c : C} (hd : d ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    addVal w ℓ (d⁻¹ ^ n * c) = addVal w ℓ c - (n : ℝ) * addVal w ℓ d := by
  have hwd : ((w d : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hd)
  have hwc : ((w c : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hc)
  have hl : Real.log ((w ℓ : ℝ≥0) : ℝ) ≠ 0 := by
    refine (Real.log_neg ?_ ?_).ne
    · exact_mod_cast h0
    · exact_mod_cast h1
  unfold addVal
  rw [map_mul, map_pow, map_inv₀]
  push_cast
  rw [Real.log_mul (pow_ne_zero _ (inv_ne_zero hwd)) hwc, Real.log_pow, Real.log_inv]
  field_simp
  ring

/- English proof (translation)
Take `⟨x, u, m, c, hx, hu, hm, hmF, ⟨hc0, hcy⟩, hdet⟩` from `h`. Establish `hdC : (d : C) ≠ 0` using `fun e => hd (Subtype.ext e)`. Establish `hsm : ∀ v : Fin (p + q) → C, d • v = (d : C) • v` using `fun v => rfl`. Establish `hinj : Function.Injective (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)`. Introduce `a b hab`.

Simplify using `only [LinearMap.lsmul_apply, hsm] at hab`. Conclude with `smul_right_injective _ hdC hab`. Use `⟨fun i => (d : C)⁻¹ • x i, u, m, (d : C)⁻¹ ^ (p + q) * c, ⟨?_, ?_⟩, hu, hm, hmF, ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hdC)) hc0, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `hx.1.units_smul (fun _ => Units.mk0 _ (inv_ne_zero hdC))`. Apply `Submodule.map_injective_of_injective hinj` to reduce the goal to its premises.

Rewrite using `[← hx.2, Submodule.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `[hsm, smul_smul, hdC]`. Rewrite using `[addVal_inv_pow_mul w ℓ h0 h1 hdC hc0, hcy]`.

Establish `: Matrix.of (fun i => (d : C)⁻¹ • x i) = (d : C)⁻¹ • Matrix.of x`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[this, Matrix.det_smul, Fintype.card_fin, hdet, mul_assoc]`.
-/
theorem detRel_of_detRel_lsmul (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (p q : ℕ) (F : Submodule C (Fin (p + q) → C))
    (X0 : Submodule w.valuationSubring (Fin (p + q) → C))
    (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F))
    (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring)
    (hd : d ≠ 0)
    (h : DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y) :
    DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * addVal w ℓ (d : C)) := by
  obtain ⟨x, u, m, c, hx, hu, hm, hmF, ⟨hc0, hcy⟩, hdet⟩ := h
  have hdC : (d : C) ≠ 0 := fun e => hd (Subtype.ext e)
  have hsm : ∀ v : Fin (p + q) → C, d • v = (d : C) • v := fun v => rfl
  have hinj : Function.Injective (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d) := by
    intro a b hab
    simp only [LinearMap.lsmul_apply, hsm] at hab
    exact smul_right_injective _ hdC hab
  refine ⟨fun i => (d : C)⁻¹ • x i, u, m, (d : C)⁻¹ ^ (p + q) * c, ⟨?_, ?_⟩, hu, hm, hmF,
    ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hdC)) hc0, ?_⟩, ?_⟩
  · exact hx.1.units_smul (fun _ => Units.mk0 _ (inv_ne_zero hdC))
  · apply Submodule.map_injective_of_injective hinj
    rw [← hx.2, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [hsm, smul_smul, hdC]
  · rw [addVal_inv_pow_mul w ℓ h0 h1 hdC hc0, hcy]
  · have : Matrix.of (fun i => (d : C)⁻¹ • x i) = (d : C)⁻¹ • Matrix.of x := by
      ext i j; simp
    rw [this, Matrix.det_smul, Fintype.card_fin, hdet, mul_assoc]

end GlobalTheory
