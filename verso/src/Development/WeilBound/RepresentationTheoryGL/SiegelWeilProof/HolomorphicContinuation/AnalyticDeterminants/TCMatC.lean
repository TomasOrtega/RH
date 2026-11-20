import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.TCMatB

noncomputable section

open Matrix ComplexConjugate

namespace PositivityTheory.Rg.Sw.LVs.TC

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `i k`. Rewrite using `[mul_diagonal, diagonal_mul, single_apply, single_apply]`. Use `split_ifs with h`. Take `⟨rfl, rfl⟩` from `h`. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules.
-/
theorem diag_single_diag (u v : Fin n → ℂ) (r s : Fin n) (c : ℂ) :
    diagonal u * single r s c * diagonal v = single r s (u r * c * v s) := by
  ext i k
  rw [mul_diagonal, diagonal_mul, single_apply, single_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    ring
  · simp

/- English proof (translation)
Unfold `InG`. Use `set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD`. Establish `hK : Dᴴ * fromBlocks (-(2 * Complex.I) • 1) 0 0 ((2 * Complex.I) • 1) * D = fromBlocks (-(2 * Complex.I) • 1) 0 0 ((2 * Complex.I) • 1)`. Rewrite using `[hD, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `[diagonal_conjTranspose]`.

Conclude with `⟨funext fun a => h1 a, funext fun a => h2 a⟩`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = (CmI n)ᴴ * ((Cm n)ᴴ * JJ n * Cm n) * CmI n := by rw [cmH_JJ_cm, hK]`. Use `_ = (Cm n * CmI n)ᴴ * JJ n * (Cm n * CmI n) := by`.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = JJ n := by rw [cm_mul_cmI, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem inG_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, star (d1 a) * d1 a = 1) (h2 : ∀ a, star (d2 a) * d2 a = 1) :
    InG (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n) := by
  unfold InG
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  have hK : Dᴴ * fromBlocks (-(2 * Complex.I) • 1) 0 0 ((2 * Complex.I) • 1) * D =
      fromBlocks (-(2 * Complex.I) • 1) 0 0 ((2 * Complex.I) • 1) := by
    rw [hD, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [diagonal_conjTranspose]
    exact ⟨funext fun a => h1 a, funext fun a => h2 a⟩
  calc (Cm n * D * CmI n)ᴴ * JJ n * (Cm n * D * CmI n)
      = (CmI n)ᴴ * (Dᴴ * ((Cm n)ᴴ * JJ n * Cm n) * D) * CmI n := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = (CmI n)ᴴ * ((Cm n)ᴴ * JJ n * Cm n) * CmI n := by rw [cmH_JJ_cm, hK]
    _ = (Cm n * CmI n)ᴴ * JJ n * (Cm n * CmI n) := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = JJ n := by rw [cm_mul_cmI, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Use `set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD`. Use `set D' : M2 n := fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) with hD'`. Establish `hDD : D * D' = 1`. Rewrite using `[hD, hD', fromBlocks_multiply, ← fromBlocks_one]`. Simplify using `[diagonal_mul_diagonal, h1, h2]`.

Use `done`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Cm n * (D * D') * CmI n := by`. Rewrite using `[cmI_mul_cm, Matrix.mul_one]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = 1 := by rw [hDD, Matrix.mul_one, cm_mul_cmI]`.
-/
theorem prod_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) :
    Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n *
      (Cm n * fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) * CmI n) = 1 := by
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  set D' : M2 n := fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) with hD'
  have hDD : D * D' = 1 := by
    rw [hD, hD', fromBlocks_multiply, ← fromBlocks_one]
    simp [diagonal_mul_diagonal, h1, h2]
    done
  calc Cm n * D * CmI n * (Cm n * D' * CmI n) = Cm n * D * (CmI n * Cm n) * D' * CmI n := by
        simp only [Matrix.mul_assoc]
    _ = Cm n * (D * D') * CmI n := by
        rw [cmI_mul_cm, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hDD, Matrix.mul_one, cm_mul_cmI]

/- English proof (translation)
Conclude with `Matrix.inv_eq_right_inv (prod_conjDiag d1 d2 h1 h2)`.
-/
theorem inv_conjDiag (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) :
    (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n)⁻¹ =
      Cm n * fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) * CmI n := by
  exact Matrix.inv_eq_right_inv (prod_conjDiag d1 d2 h1 h2)

/- English proof (translation)
Rewrite using `[CmI, Cm, Matrix.smul_mul, Matrix.smul_mul, fromBlocks_multiply, fromBlocks_multiply]`. Use `congr 1`. Simplify using the standard rewrite rules. Use `done`.
-/
theorem cmI_N_cm (E : Matrix (Fin n) (Fin n) ℂ) :
    CmI n * fromBlocks 0 E 0 0 * Cm n = ((2 * Complex.I)⁻¹ : ℂ) • fromBlocks E E (-E) (-E) := by
  rw [CmI, Cm, Matrix.smul_mul, Matrix.smul_mul, fromBlocks_multiply, fromBlocks_multiply]
  congr 1
  simp
  done

/- English proof (translation)
Rewrite using `[inv_conjDiag d1 d2 h1 h2]`. Establish `hn : nU (single r s (1 : ℂ)) = 1 + fromBlocks 0 (single r s 1) 0 0`. Rewrite using `[nU, ← fromBlocks_one, fromBlocks_add]`. Simplify using the standard rewrite rules. Rewrite using `[hn, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, prod_conjDiag d1 d2 h1 h2, add_sub_cancel_left]`.

Use `set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD`. Use `set D' : M2 n := fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) with hD'`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by`.

Rewrite using `[cmI_N_cm]`. Use `congr 2`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul, hD, hD', fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `[diag_single_diag]`. Use `done`.
-/
theorem conj_nU (d1 d2 : Fin n → ℂ) (h1 : ∀ a, d1 a ≠ 0) (h2 : ∀ a, d2 a ≠ 0) (r s : Fin n) :
    Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n * nU (single r s 1) *
        (Cm n * fromBlocks (diagonal d1) 0 0 (diagonal d2) * CmI n)⁻¹ - 1 =
      Cm n * (((2 * Complex.I)⁻¹ : ℂ) • fromBlocks (single r s (d1 r * (d1 s)⁻¹)) (single r s (d1 r * (d2 s)⁻¹))
        (-single r s (d2 r * (d1 s)⁻¹)) (-single r s (d2 r * (d2 s)⁻¹))) * CmI n := by
  rw [inv_conjDiag d1 d2 h1 h2]
  have hn : nU (single r s (1 : ℂ)) = 1 + fromBlocks 0 (single r s 1) 0 0 := by
    rw [nU, ← fromBlocks_one, fromBlocks_add]
    simp
  rw [hn, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, prod_conjDiag d1 d2 h1 h2, add_sub_cancel_left]
  set D : M2 n := fromBlocks (diagonal d1) 0 0 (diagonal d2) with hD
  set D' : M2 n := fromBlocks (diagonal fun a => (d1 a)⁻¹) 0 0 (diagonal fun a => (d2 a)⁻¹) with hD'
  calc Cm n * D * CmI n * fromBlocks 0 (single r s 1) 0 0 * (Cm n * D' * CmI n)
      = Cm n * (D * (CmI n * fromBlocks 0 (single r s 1) 0 0 * Cm n) * D') * CmI n := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [cmI_N_cm]
        congr 2
        rw [Matrix.mul_smul, Matrix.smul_mul, hD, hD', fromBlocks_multiply, fromBlocks_multiply]
        simp [diag_single_diag]
        done

end PositivityTheory.Rg.Sw.LVs.TC
