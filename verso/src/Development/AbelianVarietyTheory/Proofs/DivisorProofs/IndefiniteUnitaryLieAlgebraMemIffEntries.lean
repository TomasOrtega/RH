import Formalism.RealPlaceAnalysis.SmoothOnGVIff
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory

/- English proof (translation)
Introduce `n ε Z`. Establish `key : ∀ a b, (Zᴴ * Jm ε + Jm ε * Z) a b = (starRingEnd ℂ) (Z b a) * (if ε b then (1 : ℂ) else -1) + (if ε a then (1 : ℂ) else -1) * Z a b`. Introduce `a b`. Simplify using `[Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`. Unfold `inG`.

Prove the components needed by the constructor for the conclusion. Introduce `h a b`. Establish `hb` using `congrFun (congrFun h b) a`. Rewrite `hb` using `[key]`. Simplify using `only [Matrix.zero_apply] at hb`.

Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>`. Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε b) with hb' | hb' <;>`. Apply the tactic sequence `simp only [ha, hb', if_true, Bool.false_eq_true, if_false] at hb ⊢ <;>`. Apply the tactic sequence `first | linear_combination hb | linear_combination -hb`. Introduce `h`.

Use extensionality with `a b`. Rewrite using `[key]`. Simplify using `only [Matrix.zero_apply]`. Establish `hb` using `h b a`. Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>`.

Apply the tactic sequence `rcases Bool.eq_false_or_eq_true (ε b) with hb' | hb' <;>`. Apply the tactic sequence `simp only [ha, hb', if_true, Bool.false_eq_true, if_false] at hb ⊢ <;>`. Apply the tactic sequence `first | linear_combination hb | linear_combination -hb`.
-/
theorem pcLieEntry : ∀ (n : ℕ) (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ), inG ε Z ↔ ∀ a b, (starRingEnd ℂ) (Z a b) = -((if ε a then (1 : ℂ) else -1) * (if ε b then (1 : ℂ) else -1) * Z b a) := by
  intro n ε Z
  have key : ∀ a b, (Zᴴ * Jm ε + Jm ε * Z) a b = (starRingEnd ℂ) (Z b a) * (if ε b then (1 : ℂ) else -1) + (if ε a then (1 : ℂ) else -1) * Z a b := by
    intro a b
    simp [Jm, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  unfold inG
  constructor
  · intro h a b
    have hb := congrFun (congrFun h b) a
    rw [key] at hb
    simp only [Matrix.zero_apply] at hb
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb' | hb' <;>
      simp only [ha, hb', if_true, Bool.false_eq_true, if_false] at hb ⊢ <;>
      first | linear_combination hb | linear_combination -hb
  · intro h
    ext a b
    rw [key]
    simp only [Matrix.zero_apply]
    have hb := h b a
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (ε b) with hb' | hb' <;>
      simp only [ha, hb', if_true, Bool.false_eq_true, if_false] at hb ⊢ <;>
      first | linear_combination hb | linear_combination -hb

end GlobalTheory
