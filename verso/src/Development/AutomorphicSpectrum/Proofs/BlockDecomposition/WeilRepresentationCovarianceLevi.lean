import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixMul

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCovar

variable {D : D7} {n : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem heis_apply (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) (v : Mx D V.rank (n + n)) (Φ : Mx D V.rank n → ℂ)
    (z : Mx D V.rank n) : PositivityTheory.GramSchwartzFunctions.EC.Heisenberg₂ ψ V v Φ z =
      ψ (trA (Matrix.trace (GlobalTheory.StdUnn.inner V z (yPart v))) + halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v)))) *
        Φ (z + xPart v) := rfl

/- English proof (translation)
Establish `h1 : (a⁻¹).1 * a.1 = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `h2 : adj a.1 * adj (a⁻¹).1 = 1`. Use `adj_mul (a⁻¹).1 a.1` as an intermediate fact. Rewrite `this` using `[show HMul.hMul (a⁻¹).1 a.1 = (1 : Mx D n n) from h1, adj_one]`.

Conclude with `this.symm`. Establish `h3 : blk4 (a⁻¹).1 0 0 (adj a.1) * mat g = 1`. Rewrite using `[hg, submatrix_fromBlocks_mul]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h1, h2]`. Conclude with `block_matrix_one`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem mat_inv_levi (g : G D n) (a : GL (Fin n) (AE D)) (hg : mat g = blk4 a.1 0 0 (adj (a⁻¹).1)) :
    mat g⁻¹ = blk4 (a⁻¹).1 0 0 (adj a.1) := by
  have h1 : (a⁻¹).1 * a.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : adj a.1 * adj (a⁻¹).1 = 1 := by
    have := adj_mul (a⁻¹).1 a.1
    rw [show HMul.hMul (a⁻¹).1 a.1 = (1 : Mx D n n) from h1, adj_one] at this
    exact this.symm
  have h3 : blk4 (a⁻¹).1 0 0 (adj a.1) * mat g = 1 := by
    rw [hg, submatrix_fromBlocks_mul]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, h1, h2]
    exact block_matrix_one
  calc mat g⁻¹ = (blk4 (a⁻¹).1 0 0 (adj a.1) * mat g) * mat g⁻¹ := by rw [h3, Matrix.one_mul]
    _ = blk4 (a⁻¹).1 0 0 (adj a.1) := by rw [Matrix.mul_assoc, mat_mul_inv', Matrix.mul_one]

/- English proof (translation)
Simplify using `only [GlobalTheory.StdUnn.inner, adj_mul]`. Rewrite using `[Matrix.mul_assoc, Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem trace_inner_levi (V : HSp D) (z y : Mx D V.rank n) (a : Mx D n n) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (HMul.hMul z a : Mx D V.rank n) y) =
      Matrix.trace (GlobalTheory.StdUnn.inner V z (HMul.hMul y (adj a) : Mx D V.rank n)) := by
  simp only [GlobalTheory.StdUnn.inner, adj_mul]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `h1 : (a⁻¹).1 * a.1 = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Establish `h2 : adj a.1 * adj (a⁻¹).1 = 1`. Use `adj_mul (a⁻¹).1 a.1` as an intermediate fact. Rewrite `this` using `[show HMul.hMul (a⁻¹).1 a.1 = (1 : Mx D n n) from h1, adj_one]`.

Conclude with `this.symm`. Simplify using `only [GlobalTheory.StdUnn.inner, adj_mul]`. Rewrite using `[Matrix.mul_assoc, Matrix.trace_mul_comm]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h2, Matrix.mul_one]`.
-/
theorem trace_inner_levi_both (V : HSp D) (x y : Mx D V.rank n) (a : GL (Fin n) (AE D)) :
    Matrix.trace (GlobalTheory.StdUnn.inner V (HMul.hMul x (a⁻¹).1 : Mx D V.rank n) (HMul.hMul y (adj a.1) : Mx D V.rank n)) =
      Matrix.trace (GlobalTheory.StdUnn.inner V x y) := by
  have h1 : (a⁻¹).1 * a.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : adj a.1 * adj (a⁻¹).1 = 1 := by
    have := adj_mul (a⁻¹).1 a.1
    rw [show HMul.hMul (a⁻¹).1 a.1 = (1 : Mx D n n) from h1, adj_one] at this
    exact this.symm
  simp only [GlobalTheory.StdUnn.inner, adj_mul]
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]
  rw [h2, Matrix.mul_one]

/- English proof (translation)
Introduce `D n V ψ χ θ μ ω hW g a hg v Φ Ψ hΨ`. Establish `hinv` using `mat_inv_levi g a hg`. Establish `hx : xPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = HMul.hMul (xPart v) (a⁻¹).1`. Rewrite using `[hinv, x_part_mul_block, Matrix.mul_zero, add_zero]`. Establish `hy : yPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = HMul.hMul (yPart v) (adj a.1)`.

Rewrite using `[hinv, y_part_mul_block, Matrix.mul_zero, zero_add]`. Establish `h1 : (a⁻¹).1 * a.1 = 1`. Rewrite using `[← Units.val_mul, inv_mul_cancel, Units.val_one]`. Use function extensionality and compare the values at `z`. Rewrite using `[hW.levi g a hg Ψ z, hΨ]`.

Rewrite using `[heis_apply, heis_apply, hx, hy, hW.levi g a hg Φ, trace_inner_levi V z (yPart v) a.1, trace_inner_levi_both]`. Establish `e3 : HMul.hMul (z + HMul.hMul (xPart v) (a⁻¹).1 : Mx D V.rank n) a.1 = (HMul.hMul z a.1 + xPart v : Mx D V.rank n)`. Rewrite using `[Matrix.add_mul, Matrix.mul_assoc, h1, Matrix.mul_one]`. Rewrite using `[e3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem covAt_levi : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → ∀ (g : G D n) (a : GL (Fin n) (AE D)), mat g = blk4 a.1 0 0 (adj (a⁻¹).1) → CovAt ψ V ω g := by
  intro D n V ψ χ θ μ ω hW g a hg v Φ Ψ hΨ
  have hinv := mat_inv_levi g a hg
  have hx : xPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = HMul.hMul (xPart v) (a⁻¹).1 := by
    rw [hinv, x_part_mul_block, Matrix.mul_zero, add_zero]
  have hy : yPart (HMul.hMul v (mat g⁻¹) : Mx D V.rank (n + n)) = HMul.hMul (yPart v) (adj a.1) := by
    rw [hinv, y_part_mul_block, Matrix.mul_zero, zero_add]
  have h1 : (a⁻¹).1 * a.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  funext z
  rw [hW.levi g a hg Ψ z, hΨ]
  rw [heis_apply, heis_apply, hx, hy, hW.levi g a hg Φ, trace_inner_levi V z (yPart v) a.1, trace_inner_levi_both]
  have e3 : HMul.hMul (z + HMul.hMul (xPart v) (a⁻¹).1 : Mx D V.rank n) a.1 =
      (HMul.hMul z a.1 + xPart v : Mx D V.rank n) := by
    rw [Matrix.add_mul, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [e3]
  ring

end GlobalTheory.CompanionTheory.EisCovar
