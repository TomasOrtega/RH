import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZphiPowPr
open Matrix

namespace GlobalTheory.ZarhinFam

/- English proof (translation)
Apply the tactic sequence `rcases i with a | a <;> rcases j with b | b <;>`. Simplify using `only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply, Matrix.zero_apply, smul_eq_mul]`. Apply the tactic sequence `all_goals (try simp only [@eq_comm _ b a])`. Apply the tactic sequence `all_goals (try split_ifs)`. Apply the tactic sequence `all_goals ring`.
-/
theorem zW_symm_blocks (d : ℕ) (i j : Fin 4 ⊕ Fin 4) :
    Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 i j +
      Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) ((2 : ℤ) • (quat d).transpose) 0 1 j i =
    2 * Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1 i j := by
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, Matrix.transpose_apply,
      Matrix.zero_apply, smul_eq_mul]
  all_goals (try simp only [@eq_comm _ b a])
  all_goals (try split_ifs)
  all_goals ring

/- English proof (translation)
Use `set x : Matrix (Fin 4) (Fin 4) ℝ := (quat d).map (Int.cast : ℤ → ℝ) with hx`. Establish `hxx : xᵀ * x = ((d : ℝ) - 1) • (1 : Matrix (Fin 4) (Fin 4) ℝ)`. Establish `h1 : (((d - 1 : ℕ) : ℤ) : ℝ) = (d : ℝ) - 1`. Rewrite using `[Int.cast_natCast, Nat.cast_sub (by omega)]; simp`. Use extensionality with `i j`.

Establish `h0` using `congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun (quat_transpose_mul d) i) j)`. Simplify using `only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul, hx, Matrix.map_apply] at h0 ⊢`. Rewrite using `[h0]`. Apply the tactic sequence `split_ifs <;> simp [Nat.cast_sub (show 1 ≤ d by omega)]`. Use `set C : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 x 1 with hC`.

Use `set C' : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 (-x) 1 with hC'`. Establish `hCC : C' * C = 1`. Rewrite using `[hC, hC', Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]`. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective C.mulVec`.

Introduce `v w hvw`. Use `congrArg (C'.mulVec) hvw` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec, hCC]`. Establish `key : Cᴴ * 1 * C = (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map (Int.cast : ℤ → ℝ)`. Rewrite using `[Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial, hC, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_map]`.

Use `congr 1`. Rewrite using `[Matrix.transpose_one, Matrix.one_mul, hxx]`. Use extensionality with `i j`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Simplify using `[hx, Matrix.transpose_map]`. Simplify using `[hx]`. Simplify using the standard rewrite rules. Rewrite using `[← key]`. Conclude with `Matrix.PosDef.one.conjTranspose_mul_mul_same hinj`.
-/
theorem zarhin_block_posDef {d : ℕ} (hd : 0 < d) :
    (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map
      (Int.cast : ℤ → ℝ) |>.PosDef := by
  set x : Matrix (Fin 4) (Fin 4) ℝ := (quat d).map (Int.cast : ℤ → ℝ) with hx
  have hxx : xᵀ * x = ((d : ℝ) - 1) • (1 : Matrix (Fin 4) (Fin 4) ℝ) := by
    have h1 : (((d - 1 : ℕ) : ℤ) : ℝ) = (d : ℝ) - 1 := by
      rw [Int.cast_natCast, Nat.cast_sub (by omega)]; simp
    ext i j
    have h0 := congrArg (Int.cast : ℤ → ℝ) (congrFun (congrFun (quat_transpose_mul d) i) j)
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      Int.cast_sum, Int.cast_mul, hx, Matrix.map_apply] at h0 ⊢
    rw [h0]
    split_ifs <;> simp [Nat.cast_sub (show 1 ≤ d by omega)]
  set C : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 x 1 with hC
  set C' : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℝ := Matrix.fromBlocks 1 0 (-x) 1 with hC'
  have hCC : C' * C = 1 := by
    rw [hC, hC', Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]; simp
  have hinj : Function.Injective C.mulVec := by
    intro v w hvw
    have := congrArg (C'.mulVec) hvw
    simpa [Matrix.mulVec_mulVec, hCC] using this
  have key : Cᴴ * 1 * C =
      (Matrix.fromBlocks ((d : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) (quat d).transpose (quat d) 1).map
        (Int.cast : ℤ → ℝ) := by
    rw [Matrix.mul_one, Matrix.conjTranspose_eq_transpose_of_trivial, hC, Matrix.fromBlocks_transpose,
      Matrix.fromBlocks_multiply, Matrix.fromBlocks_map]
    congr 1
    · rw [Matrix.transpose_one, Matrix.one_mul, hxx]; ext i j
      rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
        Matrix.one_apply]
      split_ifs <;> simp
    · simp [hx, Matrix.transpose_map]
    · simp [hx]
    · simp
  rw [← key]
  exact Matrix.PosDef.one.conjTranspose_mul_mul_same hinj

/- English proof (translation)
Introduce `d hd`. Establish `hsig : Function.Injective sig`. Introduce `a b h`. Use `revert a b h`. Evaluate the decidable proposition.

Establish `h` using `((zarhin_block_posDef hd).smul (a := (2 : ℝ)) two_pos).submatrix hsig`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k l`. Establish `e` using `zW_symm_blocks d (sig k) (sig l)`. Simplify using `only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul]`.

Rewrite using `[zW, zW, e]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zW_symm_posDef : ∀ (d : ℕ), 0 < d →
    ((GlobalTheory.ZarhinFam.zW d + (GlobalTheory.ZarhinFam.zW d).transpose).map (Int.cast : ℤ → ℝ)).PosDef := by
  intro d hd
  have hsig : Function.Injective sig := by
    intro a b h; revert a b h; decide
  have h := ((zarhin_block_posDef hd).smul (a := (2 : ℝ)) two_pos).submatrix hsig
  convert h using 1
  ext k l
  have e := zW_symm_blocks d (sig k) (sig l)
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Matrix.smul_apply, smul_eq_mul]
  rw [zW, zW, e]
  push_cast
  ring

end GlobalTheory.ZarhinFam
