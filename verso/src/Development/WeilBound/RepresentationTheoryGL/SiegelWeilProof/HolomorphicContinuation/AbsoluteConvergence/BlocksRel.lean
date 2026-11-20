import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GaussPart

noncomputable section

open Matrix Set Filter Topology

namespace PositivityTheory.Rg.Sw.AbsSt.DF

open PositivityTheory.Rg.Sw

variable {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_mul (g h : GR n) : mR (g * h) = mR g * mR h := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_one : mR (1 : GR n) = 1 := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext e)`.
-/
theorem ext_mR {g h : GR n} (e : mR g = mR h) : g = h := Subtype.ext (Units.ext e)

def dg (X : Fin n → ℝ) (s : ℝ) : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => ((Real.exp (s * X j) : ℝ) : ℂ)

/- English proof (translation)
Rewrite using `[dg, dg, dg, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[← Complex.ofReal_mul, ← Real.exp_add, add_mul]`.
-/
theorem dg_mul (X : Fin n → ℝ) (s s' : ℝ) : dg X s * dg X s' = dg X (s + s') := by
  rw [dg, dg, dg, diagonal_mul_diagonal]
  congr 1
  funext j
  rw [← Complex.ofReal_mul, ← Real.exp_add, add_mul]

/- English proof (translation)
Simplify using `[dg]`.
-/
theorem dg_zero (X : Fin n → ℝ) : dg X 0 = 1 := by
  simp [dg]

/- English proof (translation)
Rewrite using `[h]`. Simplify using `only [dg, neg_mul]`.
-/
theorem isDil_iff {X : Fin n → ℝ} {s : ℝ} {g : GR n} (h : IsDil X s g) :
    mR g = fromBlocks (dg X s) 0 0 (dg X (-s)) := by
  rw [h]
  simp only [dg, neg_mul]

/- English proof (translation)
Apply `ext_mR` to reduce the goal to its premises. Rewrite using `[mR_mul, isDil_iff (ha _), isDil_iff (ha _), isDil_iff (ha _), fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, dg_mul, neg_add]`.
-/
theorem dil_mul {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (s s' : ℝ) :
    a (s + s') = a s * a s' := by
  apply ext_mR
  rw [mR_mul, isDil_iff (ha _), isDil_iff (ha _), isDil_iff (ha _), fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, dg_mul, neg_add]

/- English proof (translation)
Apply `ext_mR` to reduce the goal to its premises. Rewrite using `[isDil_iff (ha _), mR_one, neg_zero, dg_zero, fromBlocks_one]`.
-/
theorem dil_zero {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) : a 0 = 1 := by
  apply ext_mR
  rw [isDil_iff (ha _), mR_one, neg_zero, dg_zero, fromBlocks_one]

/- English proof (translation)
Use `show toBlocks₂₁ (mR (a s)) = 0`. Rewrite using `[isDil_iff (ha s), toBlocks_fromBlocks₂₁]`.
-/
theorem dil_up {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (s : ℝ) : IsUp (a s) := by
  show toBlocks₂₁ (mR (a s)) = 0
  rw [isDil_iff (ha s), toBlocks_fromBlocks₂₁]

/- English proof (translation)
Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[← dil_mul ha, add_neg_cancel, dil_zero ha]`.
-/
theorem dil_inv {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) (s : ℝ) : (a s)⁻¹ = a (-s) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← dil_mul ha, add_neg_cancel, dil_zero ha]

/- English proof (translation)
Use `show toBlocks₂₁ (mR (y * g)) = 0`. Establish `hy' : toBlocks₂₁ (mR y) = 0` using `hy`. Establish `hg' : toBlocks₂₁ (mR g) = 0` using `hg`. Rewrite using `[mR_mul, ← fromBlocks_toBlocks (mR y), ← fromBlocks_toBlocks (mR g), hy', hg', fromBlocks_multiply, toBlocks_fromBlocks₂₁]`. Simplify using the standard rewrite rules.
-/
theorem up_mul {y g : GR n} (hy : IsUp y) (hg : IsUp g) : IsUp (y * g) := by
  show toBlocks₂₁ (mR (y * g)) = 0
  have hy' : toBlocks₂₁ (mR y) = 0 := hy
  have hg' : toBlocks₂₁ (mR g) = 0 := hg
  rw [mR_mul, ← fromBlocks_toBlocks (mR y), ← fromBlocks_toBlocks (mR g), hy', hg',
    fromBlocks_multiply, toBlocks_fromBlocks₂₁]
  simp

/- English proof (translation)
Establish `hc : Continuous fun s : ℝ => fromBlocks (dg X s) 0 0 (dg X (-s))`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Apply the tactic sequence `simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, dg, diagonal_apply, Matrix.zero_apply] <;> (try split_ifs) <;> fun_prop`. Apply `continuous_induced_rng.2` to reduce the goal to its premises.

Use `Units.continuous_iff.2 ⟨hc.congr fun s => (isDil_iff (ha s)).symm, ?_⟩` and prove the remaining obligations. Use `(hc.comp continuous_neg).congr fun s => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply]`. Rewrite using `[← isDil_iff (ha (-s)), ← dil_inv ha s]`. Both sides reduce to the same expression.
-/
theorem cont_dil {X : Fin n → ℝ} {a : ℝ → GR n} (ha : ∀ s, IsDil X s (a s)) : Continuous a := by
  have hc : Continuous fun s : ℝ => fromBlocks (dg X s) 0 0 (dg X (-s)) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        dg, diagonal_apply, Matrix.zero_apply] <;> (try split_ifs) <;> fun_prop
  apply continuous_induced_rng.2
  refine Units.continuous_iff.2 ⟨hc.congr fun s => (isDil_iff (ha s)).symm, ?_⟩
  refine (hc.comp continuous_neg).congr fun s => ?_
  simp only [Function.comp_apply]
  rw [← isDil_iff (ha (-s)), ← dil_inv ha s]
  rfl

/- English proof (translation)
Simplify using `only [JJ, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add]`. Rewrite using `[← fromBlocks_one, fromBlocks_neg, neg_zero]`.
-/
theorem JJ_mul_self : JJ n * JJ n = -1 := by
  simp only [JJ, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add]
  rw [← fromBlocks_one, fromBlocks_neg, neg_zero]

end PositivityTheory.Rg.Sw.AbsSt.DF
