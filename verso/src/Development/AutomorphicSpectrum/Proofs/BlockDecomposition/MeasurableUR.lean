import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Sec2

noncomputable section

open MeasureTheory Matrix Complex
open Ad3 Ad3.LR Ad3.K.GL2LocalData Ad3.K.GL2LocalData.WR GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst

namespace GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.Push

def uR (ε : Bool) (θ : ℝ) : Fin 2 → ℝ := ![-Real.sin θ, if ε then -Real.cos θ else Real.cos θ]

def sgE (ε : Bool) : ℝ := if ε then -1 else 1

/- English proof (translation)
Apply the tactic sequence `cases ε <;> simp [sgE]`.
-/
theorem sgE_ne_zero (ε : Bool) : sgE ε ≠ 0 := by
  cases ε <;> simp [sgE]

/- English proof (translation)
Establish `hd : (!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0`. Rewrite using `[Matrix.det_fin_two_of]`. Use `Real.sin_sq_add_cos_sq θ` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Simplify using `only [rotR, dif_pos hd]`.

Both sides reduce to the same expression.
-/
theorem rotR_val (θ : ℝ) :
    (rotR θ).val = !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] := by
  have hd : (!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    have := Real.sin_sq_add_cos_sq θ
    nlinarith
  simp only [rotR, dif_pos hd]
  rfl

/- English proof (translation)
Take `⟨a, b, θ⟩` from `p`. Apply the tactic sequence `cases ε <;>`. Simplify using `only [hIw, kR, Units.val_mul, rotR_val]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`.

Simplify using `[dg2, sgE, Matrix.mul_apply, Fin.sum_univ_two]`.
-/
theorem hIw_val (ε : Bool) (p : ℝˣ × ℝˣ × ℝ) :
    (hIw ε p).val = !![((p.1 : ℝ) * p.2.1) * Real.cos p.2.2, ((p.1 : ℝ) * p.2.1) * Real.sin p.2.2 * sgE ε;
      -((p.2.1 : ℝ) * Real.sin p.2.2), (p.2.1 : ℝ) * Real.cos p.2.2 * sgE ε] := by
  obtain ⟨a, b, θ⟩ := p
  cases ε <;>
  · simp only [hIw, kR, Units.val_mul, rotR_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dg2, sgE, Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Establish `h` using `hIw_val ε p`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use extensionality with `i fin_cases i`. Simplify using `[Psi, h, uR]`. Apply the tactic sequence `cases ε <;> simp [Psi, h, uR, sgE]`.

Simplify using `only [Psi, h, Matrix.det_fin_two_of]`. Use `Real.sin_sq_add_cos_sq p.2.2` as an intermediate fact. Establish `e : sgE ε * (p.1 : ℝ) * (p.2.1 : ℝ) ^ 2 = sgE ε * (p.1 : ℝ) * (p.2.1 : ℝ) ^ 2 * (Real.sin p.2.2 ^ 2 + Real.cos p.2.2 ^ 2)`. Rewrite using `[this, mul_one]`. Rewrite using `[e]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem Psi_eq (ε : Bool) (p : ℝˣ × ℝˣ × ℝ) :
    Psi ε p = ((p.2.1 : ℝ) • uR ε p.2.2, sgE ε * (p.1 : ℝ) * (p.2.1 : ℝ) ^ 2) := by
  have h := hIw_val ε p
  refine Prod.ext ?_ ?_
  · ext i
    fin_cases i
    · simp [Psi, h, uR]
    · cases ε <;> simp [Psi, h, uR, sgE]
  · simp only [Psi, h, Matrix.det_fin_two_of]
    have := Real.sin_sq_add_cos_sq p.2.2
    have e : sgE ε * (p.1 : ℝ) * (p.2.1 : ℝ) ^ 2 =
        sgE ε * (p.1 : ℝ) * (p.2.1 : ℝ) ^ 2 * (Real.sin p.2.2 ^ 2 + Real.cos p.2.2 ^ 2) := by
      rw [this, mul_one]
    rw [e]; ring

/- English proof (translation)
Use `measurable_pi_iff.2 fun i => ?_` and prove the remaining obligations. Use `fin_cases i`. Simplify `Real.measurable_sin` using `[uR]`. Consider the cases of `ε`. Simplify `Real.measurable_cos` using `[uR]`.

Simplify `Real.measurable_cos` using `[uR]`.
-/
theorem measurable_uR (ε : Bool) : Measurable (uR ε) := by
  refine measurable_pi_iff.2 fun i => ?_
  fin_cases i
  · simpa [uR] using Real.measurable_sin
  · cases ε
    · simpa [uR] using Real.measurable_cos
    · simpa [uR] using Real.measurable_cos

end GlobalTheory.CompanionTheory.GL2LocalData.RealWhittakerFirst.Push

end
