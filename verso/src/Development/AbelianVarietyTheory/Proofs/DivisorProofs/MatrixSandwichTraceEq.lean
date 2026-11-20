import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Establish `hdet : G.det * F.det = μ ^ h`. Rewrite using `[← Matrix.det_mul, hGF, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]`. Establish `hF : F.det ≠ 0`. Introduce `h0`. Rewrite `hdet` using `[h0, mul_zero]`.

Conclude with `pow_ne_zero h hμ hdet.symm`. Establish `hFG : F * G = μ • (1 : Matrix (Fin h) (Fin h) A)`. Establish `h1 : (F * G - μ • (1 : Matrix (Fin h) (Fin h) A)) * F = 0`. Rewrite using `[sub_mul, Matrix.mul_assoc, hGF, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, sub_self]`. Establish `h2 : F.det • (F * G - μ • (1 : Matrix (Fin h) (Fin h) A)) = 0`.

Use `congrArg (· * F.adjugate) h1` as an intermediate fact. Simplify using `only [Matrix.zero_mul] at this`. Rewrite `this` using `[Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one]`. Conclude with `this`. Break down `smul_eq_zero.mp h2 with h3 | h3` into its components or cases.

Conclude with `absurd h3 hF`. Conclude with `sub_eq_zero.mp h3`. Establish `hXG : X * G = G * Y`. Establish `e : μ • (X * G) = μ • (G * Y)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]`. Use `_ = G * (Y * (F * G)) := by`. Rewrite using `[Matrix.mul_assoc G F X, hFX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (G * Y)]`. Use `_ = μ • (G * Y) := by`. Rewrite using `[hFG, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul]`.

Conclude with `smul_right_injective _ hμ e`. Use `⟨hFG, hXG, ?_⟩` and prove the remaining obligations. Establish `e : μ * Y.trace = μ * X.trace`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, Matrix.trace_mul_comm F (G * Y), Matrix.mul_assoc]`.

Use `_ = ((G * F) * X).trace := by rw [← hFX, Matrix.mul_assoc]`. Use `_ = (μ • X).trace := by rw [hGF, Matrix.smul_mul, Matrix.one_mul]`. Use `_ = μ * X.trace := by rw [Matrix.trace_smul, smul_eq_mul]`. Conclude with `mul_left_cancel₀ hμ e`.
-/
theorem trace_eq_of_intertwined_by_quasi_inverse (A : Type) [CommRing A] [IsDomain A] (h : ℕ) (μ : A)
    (F G X Y : Matrix (Fin h) (Fin h) A) (hμ : μ ≠ 0)
    (hGF : G * F = μ • (1 : Matrix (Fin h) (Fin h) A)) (hFX : F * X = Y * F) :
    F * G = μ • (1 : Matrix (Fin h) (Fin h) A) ∧ X * G = G * Y ∧ Y.trace = X.trace := by
  have hdet : G.det * F.det = μ ^ h := by
    rw [← Matrix.det_mul, hGF, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  have hF : F.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hdet
    exact pow_ne_zero h hμ hdet.symm
  have hFG : F * G = μ • (1 : Matrix (Fin h) (Fin h) A) := by
    have h1 : (F * G - μ • (1 : Matrix (Fin h) (Fin h) A)) * F = 0 := by
      rw [sub_mul, Matrix.mul_assoc, hGF, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul, sub_self]
    have h2 : F.det • (F * G - μ • (1 : Matrix (Fin h) (Fin h) A)) = 0 := by
      have := congrArg (· * F.adjugate) h1
      simp only [Matrix.zero_mul] at this
      rw [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at this
      exact this
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 hF
    · exact sub_eq_zero.mp h3
  have hXG : X * G = G * Y := by
    have e : μ • (X * G) = μ • (G * Y) := by
      calc μ • (X * G) = (G * F) * X * G := by
              rw [hGF, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
        _ = G * (Y * (F * G)) := by
              rw [Matrix.mul_assoc G F X, hFX, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
                Matrix.mul_assoc (G * Y)]
        _ = μ • (G * Y) := by
              rw [hFG, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul]
    exact smul_right_injective _ hμ e
  refine ⟨hFG, hXG, ?_⟩
  have e : μ * Y.trace = μ * X.trace := by
    calc μ * Y.trace = (μ • Y).trace := by rw [Matrix.trace_smul, smul_eq_mul]
      _ = ((F * G) * Y).trace := by rw [hFG, Matrix.smul_mul, Matrix.one_mul]
      _ = (G * (Y * F)).trace := by
            rw [Matrix.mul_assoc, Matrix.trace_mul_comm F (G * Y), Matrix.mul_assoc]
      _ = ((G * F) * X).trace := by rw [← hFX, Matrix.mul_assoc]
      _ = (μ • X).trace := by rw [hGF, Matrix.smul_mul, Matrix.one_mul]
      _ = μ * X.trace := by rw [Matrix.trace_smul, smul_eq_mul]
  exact mul_left_cancel₀ hμ e

end GlobalTheory
