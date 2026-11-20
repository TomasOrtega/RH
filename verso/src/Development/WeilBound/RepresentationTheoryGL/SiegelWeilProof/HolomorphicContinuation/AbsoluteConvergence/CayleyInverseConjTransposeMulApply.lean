import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacOut
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.GramDiagUnitary
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.CayleyMulConjTranspose

open scoped Matrix
open Matrix

noncomputable section

namespace PositivityTheory.Rg.Sw.AbsSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.KAKA PositivityTheory.Rg.Sw.KAKB

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `rcases i with i | i <;> rcases j with j | j <;>`. Simplify using `[JJ, fromBlocks_multiply, Matrix.one_apply]`.
-/
theorem JJ_sq : JJ n * JJ n = -1 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [JJ, fromBlocks_multiply, Matrix.one_apply]

/- English proof (translation)
Simplify using `[C1, conjTranspose_smul]`.
-/
theorem cayley_inverse_conjTranspose : (C1 n)ᴴ = (1 / 2 : ℂ) • C0 n := by
  simp [C1, conjTranspose_smul]

/- English proof (translation)
Rewrite using `[← complex_structure_cayley, Matrix.mul_assoc, cayley_mul_inverse, Matrix.mul_one]`.
-/
theorem JJ_eq : JJ n = C0 n * (Complex.I • S0 n) * C1 n := by
  rw [← complex_structure_cayley, Matrix.mul_assoc, cayley_mul_inverse, Matrix.mul_one]

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, cayley_conjTranspose_mul, Matrix.smul_mul, Matrix.one_mul]`.
-/
theorem cayley_conjTranspose_mul_apply (X : M2 n) : (C0 n)ᴴ * (C0 n * X) = (2 : ℂ) • X := by
  rw [← Matrix.mul_assoc, cayley_conjTranspose_mul, Matrix.smul_mul, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, cayley_inverse_mul, Matrix.one_mul]`.
-/
theorem cayley_inverse_mul_apply (X : M2 n) : C1 n * (C0 n * X) = X := by
  rw [← Matrix.mul_assoc, cayley_inverse_mul, Matrix.one_mul]

/- English proof (translation)
Rewrite using `[← Matrix.mul_assoc, cayley_mul_inverse, Matrix.one_mul]`.
-/
theorem cayley_mul_inverse_apply (X : M2 n) : C0 n * (C1 n * X) = X := by
  rw [← Matrix.mul_assoc, cayley_mul_inverse, Matrix.one_mul]

def mkGR (M : M2 n) (h : InG M) : GR n :=
  have hl : (-(JJ n) * Mᴴ * JJ n) * M = 1 := by
    have h' : Mᴴ * JJ n * M = JJ n := h
    calc (-(JJ n) * Mᴴ * JJ n) * M = -(JJ n * (Mᴴ * JJ n * M)) := by simp only [Matrix.mul_assoc, Matrix.neg_mul]
      _ = 1 := by rw [h', JJ_sq, neg_neg]
  ⟨⟨M, -(JJ n) * Mᴴ * JJ n, mul_eq_one_comm.mp hl, hl⟩, h⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mR_mkGR (M : M2 n) (h : InG M) : mR (mkGR M h) = M := rfl

/- English proof (translation)
Establish `hN' : ∀ X : M2 n, Nᴴ * (S0 n * (N * X)) = S0 n * X` using `fun X => by`. Simplify using `only [← Matrix.mul_assoc, hN]`. Use `show (C0 n * N * C1 n)ᴴ * JJ n * (C0 n * N * C1 n) = JJ n`. Rewrite using `[JJ_eq]`. Simplify using `only [conjTranspose_mul, cayley_inverse_conjTranspose, Matrix.mul_assoc, cayley_conjTranspose_mul_apply, cayley_inverse_mul_apply, hN', Matrix.smul_mul, Matrix.mul_smul, smul_smul]`.

Use `module`.
-/
theorem conj_G (N : M2 n) (hN : Nᴴ * S0 n * N = S0 n) : InG (C0 n * N * C1 n) := by
  have hN' : ∀ X : M2 n, Nᴴ * (S0 n * (N * X)) = S0 n * X := fun X => by
    simp only [← Matrix.mul_assoc, hN]
  show (C0 n * N * C1 n)ᴴ * JJ n * (C0 n * N * C1 n) = JJ n
  rw [JJ_eq]
  simp only [conjTranspose_mul, cayley_inverse_conjTranspose, Matrix.mul_assoc, cayley_conjTranspose_mul_apply, cayley_inverse_mul_apply, hN',
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  module

/- English proof (translation)
Establish `hN' : ∀ X : M2 n, Nᴴ * (N * X) = X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, hN, Matrix.one_mul]`. Simplify using `only [conjTranspose_mul, cayley_inverse_conjTranspose, Matrix.mul_assoc, cayley_conjTranspose_mul_apply, hN', cayley_mul_inverse, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Evaluate the numerical expressions.
-/
theorem conj_U (N : M2 n) (hN : Nᴴ * N = 1) : (C0 n * N * C1 n)ᴴ * (C0 n * N * C1 n) = 1 := by
  have hN' : ∀ X : M2 n, Nᴴ * (N * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hN, Matrix.one_mul]
  simp only [conjTranspose_mul, cayley_inverse_conjTranspose, Matrix.mul_assoc, cayley_conjTranspose_mul_apply, hN', cayley_mul_inverse,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num

/- English proof (translation)
Simplify using `[S0, fromBlocks_conjTranspose, fromBlocks_multiply, hu, hv]`.
-/
theorem block_unitary_preserves_form (u v : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (hv : vᴴ * v = 1) :
    (fromBlocks u 0 0 v)ᴴ * S0 n * fromBlocks u 0 0 v = S0 n := by
  simp [S0, fromBlocks_conjTranspose, fromBlocks_multiply, hu, hv]

/- English proof (translation)
Rewrite using `[← fromBlocks_one]`. Simplify using `[fromBlocks_conjTranspose, fromBlocks_multiply, hu, hv]`.
-/
theorem blk_U (u v : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (hv : vᴴ * v = 1) :
    (fromBlocks u 0 0 v)ᴴ * fromBlocks u 0 0 v = 1 := by
  rw [← fromBlocks_one]
  simp [fromBlocks_conjTranspose, fromBlocks_multiply, hu, hv]

/- English proof (translation)
Rewrite using `[diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Simplify using the standard rewrite rules.
-/
theorem diag_real_conj (s : Fin n → ℝ) : (diagonal fun j => (s j : ℂ))ᴴ = diagonal fun j => (s j : ℂ) := by
  rw [diagonal_conjTranspose]
  congr 1
  funext j
  simp

/- English proof (translation)
Rewrite using `[fromBlocks_conjTranspose, diag_real_conj, diag_real_conj, S0, fromBlocks_multiply, fromBlocks_multiply]`. Apply the tactic sequence `refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[diagonal_apply, Matrix.one_apply]`. Apply the tactic sequence `all_goals first`. Consider the case `ring1`. Consider the case `linear_combination Complex.cosh_sq (X i : ℂ)`. Consider the case `linear_combination -Complex.cosh_sq (X i : ℂ)`.

Simplify using `[diagonal_apply, Matrix.one_apply, h]`.
-/
private theorem coshSinh_conjTranspose_mul_S0_mul_eq_S0 (X : Fin n → ℝ) :
    (fromBlocks (diagonal fun j => (Real.cosh (X j) : ℂ)) (diagonal fun j => (Real.sinh (X j) : ℂ))
        (diagonal fun j => (Real.sinh (X j) : ℂ)) (diagonal fun j => (Real.cosh (X j) : ℂ)))ᴴ * S0 n *
      fromBlocks (diagonal fun j => (Real.cosh (X j) : ℂ)) (diagonal fun j => (Real.sinh (X j) : ℂ))
        (diagonal fun j => (Real.sinh (X j) : ℂ)) (diagonal fun j => (Real.cosh (X j) : ℂ)) = S0 n := by
  rw [fromBlocks_conjTranspose, diag_real_conj, diag_real_conj, S0, fromBlocks_multiply,
    fromBlocks_multiply]
  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext i j
    by_cases h : i = j
    · subst h
      simp [diagonal_apply, Matrix.one_apply]
      all_goals first
        | ring1
        | linear_combination Complex.cosh_sq (X i : ℂ)
        | linear_combination -Complex.cosh_sq (X i : ℂ)
    · simp [diagonal_apply, Matrix.one_apply, h]

/- English proof (translation)
Rewrite using `[C1, cayley_conjTranspose_eq, C0, Matrix.mul_smul, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul]`. Apply the tactic sequence `refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>`. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using `[diagonal_apply, Matrix.one_apply, ← Real.cosh_add_sinh, ← Real.cosh_sub_sinh]`. Apply the tactic sequence `all_goals first`. Consider the case `ring1`. Consider the case `linear_combination (Complex.sinh (X i : ℂ) - Complex.cosh (X i : ℂ)) * Complex.I_sq`. Simplify using `[diagonal_apply, Matrix.one_apply, h]`.
-/
private theorem coshSinh_blocks_mul_C1_eq_exp_diag (X : Fin n → ℝ) :
    C0 n * fromBlocks (diagonal fun j => (Real.cosh (X j) : ℂ)) (diagonal fun j => (Real.sinh (X j) : ℂ))
        (diagonal fun j => (Real.sinh (X j) : ℂ)) (diagonal fun j => (Real.cosh (X j) : ℂ)) * C1 n =
      fromBlocks (diagonal fun j => (Real.exp (1 * X j) : ℂ)) 0 0
        (diagonal fun j => (Real.exp (-(1 * X j)) : ℂ)) := by
  rw [C1, cayley_conjTranspose_eq, C0, Matrix.mul_smul, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_smul]
  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
  · ext i j
    by_cases h : i = j
    · subst h
      simp [diagonal_apply, Matrix.one_apply, ← Real.cosh_add_sinh, ← Real.cosh_sub_sinh]
      all_goals first
        | ring1
        | linear_combination (Complex.sinh (X i : ℂ) - Complex.cosh (X i : ℂ)) * Complex.I_sq
    · simp [diagonal_apply, Matrix.one_apply, h]

/- English proof (translation)
Use `set P := N.toBlocks₁₁ with hPd`. Use `set Q := N.toBlocks₁₂ with hQd`. Use `set R := N.toBlocks₂₁ with hRd`. Use `set S := N.toBlocks₂₂ with hSd`. Establish `hNb : N = fromBlocks P Q R S` using `(fromBlocks_toBlocks N).symm`.

Establish `e` using `hN`. Rewrite `e` using `[hNb, fromBlocks_conjTranspose, S0, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul, add_zero, zero_add] at e`. Take `⟨e1, e2, -, e4⟩` from `e`. Establish `e1' : Pᴴ * P = 1 + Rᴴ * R`.

Rewrite using `[← e1]`. Normalize the expressions using the abelian group laws. Establish `e2' : Pᴴ * Q = Rᴴ * S` using `eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact e2)`. Establish `e4' : Qᴴ * Q - Sᴴ * S = -1`. Rewrite using `[sub_eq_add_neg]`.

Conclude with `e4`. Take `⟨W, l, hW1, hW2, hl⟩` from `gram_eigen R`. Establish `hl0 : ∀ j, 0 ≤ l j`. Introduce `j`. Use `open scoped ComplexOrder in`.

Establish `hp` using `(posSemidef_conjTranspose_mul_self (R * W)).diag_nonneg (i := j)`. Use `open scoped ComplexOrder in`. Rewrite `hp` using `[hl, diagonal_apply_eq]`. Use `open scoped ComplexOrder in`. Conclude with `Complex.zero_le_real.mp hp`.

Use `set X : Fin n → ℝ := fun j => Real.arsinh (Real.sqrt (l j)) with hXd`. Establish `hs2 : ∀ j, Real.sinh (X j) ^ 2 = l j` using `fun j => by`. Simplify using `only [hXd, Real.sinh_arsinh, Real.sq_sqrt (hl0 j)]`. Establish `hc2 : ∀ j, Real.cosh (X j) ^ 2 = 1 + l j` using `fun j => by`. Rewrite using `[Real.cosh_sq, hs2]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨U2, hU2, hRW⟩` from `gram_diag_unitary (R * W) (fun j => Real.sinh (X j)) (by`. Rewrite using `[hl]`. Use `congr 1`. Use function extensionality and compare the values at `j`.

Simplify using `only [hs2])`. Establish `hPW : (P * W)ᴴ * (P * W) = diagonal fun j => ((Real.cosh (X j) ^ 2 : ℝ) : ℂ)`. Establish `h1 : (P * W)ᴴ * (P * W) = Wᴴ * W + (R * W)ᴴ * (R * W)`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc Pᴴ P W, e1', Matrix.add_mul, Matrix.one_mul, Matrix.mul_add]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[h1, hW1, hl, ← diagonal_one, diagonal_add]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Rewrite using `[hc2]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨U1, hU1, hPW'⟩` from `gram_diag_unitary (P * W) (fun j => Real.cosh (X j)) hPW`. Use `set cX : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => (Real.cosh (X j) : ℂ) with hcXd`. Use `set sX : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => (Real.sinh (X j) : ℂ) with hsXd`.

Establish `hPc : P * W = U1 * cX` using `hPW'`. Establish `hRs : R * W = U2 * sX` using `hRW`. Establish `hcH : cXᴴ = cX`. Rewrite using `[hcXd]`. Conclude with `diag_real_conj (fun j => Real.cosh (X j))`.

Establish `hsH : sXᴴ = sX`. Rewrite using `[hsXd]`. Conclude with `diag_real_conj (fun j => Real.sinh (X j))`. Establish `hU1' : U1 * U1ᴴ = 1` using `mul_eq_one_comm.mp hU1`. Establish `hU2' : U2 * U2ᴴ = 1` using `mul_eq_one_comm.mp hU2`.

Establish `hcross : cX * (U1ᴴ * Q) = sX * (U2ᴴ * S)`. Establish `h1 : (P * W)ᴴ * Q = (R * W)ᴴ * S`. Simplify using `only [conjTranspose_mul, Matrix.mul_assoc, e2']`. Rewrite `h1` using `[hPc, hRs, conjTranspose_mul, conjTranspose_mul, hcH, hsH]`. Simplify `h1` using `only [Matrix.mul_assoc]`.

Use `set cI : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => ((Real.cosh (X j) : ℂ))⁻¹ with hcId`. Establish `hcne : ∀ j, (Real.cosh (X j) : ℂ) ≠ 0` using `fun j => by`. Conclude with `(Real.cosh_pos (X j)).ne'` after adjusting the coercions. Establish `hcI : cI * cX = 1`. Rewrite using `[hcId, hcXd, diagonal_mul_diagonal, ← diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `inv_mul_cancel₀ (hcne j)`. Establish `hcI' : cX * cI = 1`. Rewrite using `[hcId, hcXd, diagonal_mul_diagonal, ← diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Conclude with `mul_inv_cancel₀ (hcne j)`. Establish `hcomm : cI * sX = sX * cI`. Rewrite using `[hcId, hsXd, diagonal_mul_diagonal, diagonal_mul_diagonal]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Expand and normalize the polynomial expressions, which then agree. Take `⟨V, hVd⟩ : ∃ V, V = cI * (U2ᴴ * S)` from `⟨_, rfl⟩`. Establish `hQ' : U1ᴴ * Q = sX * V`.

Combine the equalities or inequalities in the displayed calculation. Establish `hS' : U2ᴴ * S = cX * V`. Combine the equalities or inequalities in the displayed calculation. Establish `hd : sX * sX - cX * cX = -1`. Use extensionality with `i j`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[hsXd, hcXd, diagonal_apply]`. Take the linear combination `-Complex.cosh_sq (X i : ℂ)`. Simplify using `[hsXd, hcXd, diagonal_apply, h]`.

Establish `hV : Vᴴ * V = 1`. Establish `hQQ : (U1ᴴ * Q)ᴴ * (U1ᴴ * Q) = Qᴴ * Q`. Rewrite using `[conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc U1, hU1', Matrix.one_mul]`. Establish `hSS : (U2ᴴ * S)ᴴ * (U2ᴴ * S) = Sᴴ * S`. Rewrite using `[conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc U2, hU2', Matrix.one_mul]`.

Establish `h` using `e4'`. Rewrite `h` using `[← hQQ, ← hSS, hQ', hS', conjTranspose_mul, conjTranspose_mul, hsH, hcH]`. Establish `h2 : Vᴴ * (sX * sX - cX * cX) * V = -1`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul]`. Simplify `h` using `only [Matrix.mul_assoc]`.

Rewrite `h2` using `[hd, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_inj]`. Conclude with `h2`. Use `⟨U1, U2, Wᴴ, V, X, hU1, hU2, by rw [conjTranspose_conjTranspose]; exact hW2, hV, ?_⟩` and prove the remaining obligations. Rewrite using `[hNb, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]`.

Use `fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, ← hQ', ← Matrix.mul_assoc, hU1', Matrix.one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_assoc, ← hS', ← Matrix.mul_assoc, hU2', Matrix.one_mul]`.
-/
private theorem exists_unitary_coshSinh_decomposition (N : M2 n) (hN : Nᴴ * S0 n * N = S0 n) :
    ∃ (U1 U2 W V : Matrix (Fin n) (Fin n) ℂ) (X : Fin n → ℝ),
      U1ᴴ * U1 = 1 ∧ U2ᴴ * U2 = 1 ∧ Wᴴ * W = 1 ∧ Vᴴ * V = 1 ∧
      N = fromBlocks U1 0 0 U2 *
        fromBlocks (diagonal fun j => (Real.cosh (X j) : ℂ)) (diagonal fun j => (Real.sinh (X j) : ℂ))
          (diagonal fun j => (Real.sinh (X j) : ℂ)) (diagonal fun j => (Real.cosh (X j) : ℂ)) *
        fromBlocks W 0 0 V := by
  set P := N.toBlocks₁₁ with hPd
  set Q := N.toBlocks₁₂ with hQd
  set R := N.toBlocks₂₁ with hRd
  set S := N.toBlocks₂₂ with hSd
  have hNb : N = fromBlocks P Q R S := (fromBlocks_toBlocks N).symm
  have e := hN
  rw [hNb, fromBlocks_conjTranspose, S0, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj] at e
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
    add_zero, zero_add] at e
  obtain ⟨e1, e2, -, e4⟩ := e
  have e1' : Pᴴ * P = 1 + Rᴴ * R := by
    rw [← e1]
    abel
  have e2' : Pᴴ * Q = Rᴴ * S := eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact e2)
  have e4' : Qᴴ * Q - Sᴴ * S = -1 := by
    rw [sub_eq_add_neg]
    exact e4
  obtain ⟨W, l, hW1, hW2, hl⟩ := gram_eigen R
  have hl0 : ∀ j, 0 ≤ l j := by
    intro j
    open scoped ComplexOrder in
    have hp := (posSemidef_conjTranspose_mul_self (R * W)).diag_nonneg (i := j)
    open scoped ComplexOrder in
    rw [hl, diagonal_apply_eq] at hp
    open scoped ComplexOrder in
    exact Complex.zero_le_real.mp hp
  set X : Fin n → ℝ := fun j => Real.arsinh (Real.sqrt (l j)) with hXd
  have hs2 : ∀ j, Real.sinh (X j) ^ 2 = l j := fun j => by
    simp only [hXd, Real.sinh_arsinh, Real.sq_sqrt (hl0 j)]
  have hc2 : ∀ j, Real.cosh (X j) ^ 2 = 1 + l j := fun j => by
    rw [Real.cosh_sq, hs2]
    ring
  obtain ⟨U2, hU2, hRW⟩ := gram_diag_unitary (R * W) (fun j => Real.sinh (X j)) (by
    rw [hl]
    congr 1
    funext j
    simp only [hs2])
  have hPW : (P * W)ᴴ * (P * W) = diagonal fun j => ((Real.cosh (X j) ^ 2 : ℝ) : ℂ) := by
    have h1 : (P * W)ᴴ * (P * W) = Wᴴ * W + (R * W)ᴴ * (R * W) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Pᴴ P W, e1', Matrix.add_mul, Matrix.one_mul, Matrix.mul_add]
      simp only [Matrix.mul_assoc]
    rw [h1, hW1, hl, ← diagonal_one, diagonal_add]
    congr 1
    funext j
    rw [hc2]
    push_cast
    ring
  obtain ⟨U1, hU1, hPW'⟩ := gram_diag_unitary (P * W) (fun j => Real.cosh (X j)) hPW
  set cX : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => (Real.cosh (X j) : ℂ) with hcXd
  set sX : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => (Real.sinh (X j) : ℂ) with hsXd
  have hPc : P * W = U1 * cX := hPW'
  have hRs : R * W = U2 * sX := hRW
  have hcH : cXᴴ = cX := by
    rw [hcXd]
    exact diag_real_conj (fun j => Real.cosh (X j))
  have hsH : sXᴴ = sX := by
    rw [hsXd]
    exact diag_real_conj (fun j => Real.sinh (X j))
  have hU1' : U1 * U1ᴴ = 1 := mul_eq_one_comm.mp hU1
  have hU2' : U2 * U2ᴴ = 1 := mul_eq_one_comm.mp hU2
  have hcross : cX * (U1ᴴ * Q) = sX * (U2ᴴ * S) := by
    have h1 : (P * W)ᴴ * Q = (R * W)ᴴ * S := by
      simp only [conjTranspose_mul, Matrix.mul_assoc, e2']
    rw [hPc, hRs, conjTranspose_mul, conjTranspose_mul, hcH, hsH] at h1
    simpa only [Matrix.mul_assoc] using h1
  set cI : Matrix (Fin n) (Fin n) ℂ := diagonal fun j => ((Real.cosh (X j) : ℂ))⁻¹ with hcId
  have hcne : ∀ j, (Real.cosh (X j) : ℂ) ≠ 0 := fun j => by
    exact_mod_cast (Real.cosh_pos (X j)).ne'
  have hcI : cI * cX = 1 := by
    rw [hcId, hcXd, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    exact inv_mul_cancel₀ (hcne j)
  have hcI' : cX * cI = 1 := by
    rw [hcId, hcXd, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext j
    exact mul_inv_cancel₀ (hcne j)
  have hcomm : cI * sX = sX * cI := by
    rw [hcId, hsXd, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext j
    ring
  obtain ⟨V, hVd⟩ : ∃ V, V = cI * (U2ᴴ * S) := ⟨_, rfl⟩
  have hQ' : U1ᴴ * Q = sX * V := by
    calc U1ᴴ * Q = cI * cX * (U1ᴴ * Q) := by rw [hcI, Matrix.one_mul]
      _ = cI * (sX * (U2ᴴ * S)) := by rw [Matrix.mul_assoc, hcross]
      _ = sX * V := by rw [hVd, ← Matrix.mul_assoc, hcomm, Matrix.mul_assoc]
  have hS' : U2ᴴ * S = cX * V := by
    calc U2ᴴ * S = cX * cI * (U2ᴴ * S) := by rw [hcI', Matrix.one_mul]
      _ = cX * V := by rw [hVd, Matrix.mul_assoc]
  have hd : sX * sX - cX * cX = -1 := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [hsXd, hcXd, diagonal_apply]
      linear_combination -Complex.cosh_sq (X i : ℂ)
    · simp [hsXd, hcXd, diagonal_apply, h]
  have hV : Vᴴ * V = 1 := by
    have hQQ : (U1ᴴ * Q)ᴴ * (U1ᴴ * Q) = Qᴴ * Q := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc U1,
        hU1', Matrix.one_mul]
    have hSS : (U2ᴴ * S)ᴴ * (U2ᴴ * S) = Sᴴ * S := by
      rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc U2,
        hU2', Matrix.one_mul]
    have h := e4'
    rw [← hQQ, ← hSS, hQ', hS', conjTranspose_mul, conjTranspose_mul, hsH, hcH] at h
    have h2 : Vᴴ * (sX * sX - cX * cX) * V = -1 := by
      rw [Matrix.mul_sub, Matrix.sub_mul]
      simpa only [Matrix.mul_assoc] using h
    rw [hd, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, neg_inj] at h2
    exact h2
  refine ⟨U1, U2, Wᴴ, V, X, hU1, hU2, by rw [conjTranspose_conjTranspose]; exact hW2, hV, ?_⟩
  rw [hNb, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  refine fromBlocks_inj.mpr ⟨?_, ?_, ?_, ?_⟩
  · calc P = P * W * Wᴴ := by rw [Matrix.mul_assoc, hW2, Matrix.mul_one]
      _ = U1 * cX * Wᴴ := by rw [hPc]
  · rw [Matrix.mul_assoc, ← hQ', ← Matrix.mul_assoc, hU1', Matrix.one_mul]
  · calc R = R * W * Wᴴ := by rw [Matrix.mul_assoc, hW2, Matrix.mul_one]
      _ = U2 * sX * Wᴴ := by rw [hRs]
  · rw [Matrix.mul_assoc, ← hS', ← Matrix.mul_assoc, hU2', Matrix.one_mul]

set_option maxHeartbeats 2000000 in
/- English proof (translation)
Introduce `n y`. Establish `hY : InG (mR y)` using `y.2`. Establish `hYJ : ∀ Z : M2 n, (mR y)ᴴ * (JJ n * (mR y * Z)) = JJ n * Z` using `fun Z => by`. Establish `e : (mR y)ᴴ * JJ n * mR y = JJ n` using `hY`. Simplify using `only [← Matrix.mul_assoc, e]`.

Establish `hJ' : ∀ Z : M2 n, C0 n * (S0 n * (C1 n * Z)) = (-Complex.I) • (JJ n * Z)` using `fun Z => by`. Rewrite using `[JJ_eq]`. Simplify using `only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Use `match_scalars`. Simplify using `[Complex.I_mul_I]`.

Establish `hN : (C1 n * mR y * C0 n)ᴴ * S0 n * (C1 n * mR y * C0 n) = S0 n`. Simplify using `only [conjTranspose_mul, cayley_inverse_conjTranspose, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, hJ', hYJ, complex_structure_cayley, cayley_conjTranspose_mul_apply, smul_smul]`. Use `match_scalars`. Simplify using `[Complex.I_mul_I]`. Apply the tactic sequence `all_goals ring_nf`.

Apply the tactic sequence `all_goals simp [Complex.I_sq]`. Take `⟨U1, U2, W, V, X, hU1, hU2, hW, hV, hdec⟩` from `exists_unitary_coshSinh_decomposition _ hN`. Establish `hK1G` using `conj_G _ (block_unitary_preserves_form U1 U2 hU1 hU2)`. Establish `hK1U` using `conj_U _ (blk_U U1 U2 hU1 hU2)`. Establish `hK2G` using `conj_G _ (block_unitary_preserves_form W V hW hV)`.

Establish `hK2U` using `conj_U _ (blk_U W V hW hV)`. Establish `hAG` using `conj_G _ (coshSinh_conjTranspose_mul_S0_mul_eq_S0 X)`. Use `⟨mkGR _ hK1G, mkGR _ hK2G, mkGR _ hAG, X, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show InK (mR (mkGR _ hK1G))`. Rewrite using `[mR_mkGR]`.

Conclude with `⟨hK1G, hK1U⟩`. Use `show InK (mR (mkGR _ hK2G))`. Rewrite using `[mR_mkGR]`. Conclude with `⟨hK2G, hK2U⟩`. Use `show mR (mkGR _ hAG) = _`.

Rewrite using `[mR_mkGR]`. Conclude with `coshSinh_blocks_mul_C1_eq_exp_diag X`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show mR y = mR (mkGR _ hK1G) * mR (mkGR _ hAG) * mR (mkGR _ hK2G)`.

Rewrite using `[mR_mkGR, mR_mkGR, mR_mkGR]`. Establish `hYe : mR y = C0 n * (C1 n * mR y * C0 n) * C1 n`. Simplify using `only [Matrix.mul_assoc, cayley_mul_inverse, Matrix.mul_one, cayley_mul_inverse_apply]`. Use `conv_lhs => rw [hYe, hdec]`. Simplify using `only [Matrix.mul_assoc, cayley_inverse_mul_apply]`.
-/
theorem kAK : KAK := by
  intro n y
  have hY : InG (mR y) := y.2
  have hYJ : ∀ Z : M2 n, (mR y)ᴴ * (JJ n * (mR y * Z)) = JJ n * Z := fun Z => by
    have e : (mR y)ᴴ * JJ n * mR y = JJ n := hY
    simp only [← Matrix.mul_assoc, e]
  have hJ' : ∀ Z : M2 n, C0 n * (S0 n * (C1 n * Z)) = (-Complex.I) • (JJ n * Z) := fun Z => by
    rw [JJ_eq]
    simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    match_scalars
    simp [Complex.I_mul_I]
  have hN : (C1 n * mR y * C0 n)ᴴ * S0 n * (C1 n * mR y * C0 n) = S0 n := by
    simp only [conjTranspose_mul, cayley_inverse_conjTranspose, Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul,
      hJ', hYJ, complex_structure_cayley, cayley_conjTranspose_mul_apply, smul_smul]
    match_scalars
    simp [Complex.I_mul_I]
    all_goals ring_nf
    all_goals simp [Complex.I_sq]
  obtain ⟨U1, U2, W, V, X, hU1, hU2, hW, hV, hdec⟩ := exists_unitary_coshSinh_decomposition _ hN
  have hK1G := conj_G _ (block_unitary_preserves_form U1 U2 hU1 hU2)
  have hK1U := conj_U _ (blk_U U1 U2 hU1 hU2)
  have hK2G := conj_G _ (block_unitary_preserves_form W V hW hV)
  have hK2U := conj_U _ (blk_U W V hW hV)
  have hAG := conj_G _ (coshSinh_conjTranspose_mul_S0_mul_eq_S0 X)
  refine ⟨mkGR _ hK1G, mkGR _ hK2G, mkGR _ hAG, X, ?_, ?_, ?_, ?_⟩
  · show InK (mR (mkGR _ hK1G))
    rw [mR_mkGR]
    exact ⟨hK1G, hK1U⟩
  · show InK (mR (mkGR _ hK2G))
    rw [mR_mkGR]
    exact ⟨hK2G, hK2U⟩
  · show mR (mkGR _ hAG) = _
    rw [mR_mkGR]
    exact coshSinh_blocks_mul_C1_eq_exp_diag X
  · apply Subtype.ext
    apply Units.ext
    show mR y = mR (mkGR _ hK1G) * mR (mkGR _ hAG) * mR (mkGR _ hK2G)
    rw [mR_mkGR, mR_mkGR, mR_mkGR]
    have hYe : mR y = C0 n * (C1 n * mR y * C0 n) * C1 n := by
      simp only [Matrix.mul_assoc, cayley_mul_inverse, Matrix.mul_one, cayley_mul_inverse_apply]
    conv_lhs => rw [hYe, hdec]
    simp only [Matrix.mul_assoc, cayley_inverse_mul_apply]

end PositivityTheory.Rg.Sw.AbsSt

end
