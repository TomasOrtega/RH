import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.EvenLat

def Jm (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R := Matrix.of fun _ _ => (1 : R)

def Cm (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R := 1 + Jm R n

def Am (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  ((n : R) + 1) • (1 : Matrix (Fin n) (Fin n) R) - Jm R n

def Gm (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.fromBlocks (Am R n) ((n : R) • 1) ((n : R) • 1) ((n : R) • Cm R n)

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Jm, Matrix.mul_apply]`.
-/
theorem JJ (R : Type) [CommRing R] (n : ℕ) : Jm R n * Jm R n = (n : R) • Jm R n := by
  ext i j; simp [Jm, Matrix.mul_apply]

/- English proof (translation)
Simplify using `only [Cm, Am, add_mul, one_mul, Matrix.mul_sub, Matrix.mul_smul, mul_one, JJ]`. Use `module`.
-/
theorem CA (R : Type) [CommRing R] (n : ℕ) : Cm R n * Am R n = ((n : R) + 1) • 1 := by
  simp only [Cm, Am, add_mul, one_mul, Matrix.mul_sub, Matrix.mul_smul, mul_one, JJ]
  module

/- English proof (translation)
Simplify using `only [Cm, Am, mul_add, one_mul, sub_mul, Matrix.smul_mul, mul_one, JJ]`. Use `module`.
-/
theorem AC (R : Type) [CommRing R] (n : ℕ) : Am R n * Cm R n = ((n : R) + 1) • 1 := by
  simp only [Cm, Am, mul_add, one_mul, sub_mul, Matrix.smul_mul, mul_one, JJ]
  module

/- English proof (translation)
Apply the tactic sequence `ext (i | i) (j | j) <;> by_cases h : i = j <;>`. Simplify using `[Gm, Am, Cm, Jm, Matrix.one_apply, Matrix.natCast_apply, Matrix.diagonal_apply, h]`.
-/
theorem Gmap (n : ℕ) : (Gm ℤ n).map (Int.cast : ℤ → ℝ) = Gm ℝ n := by
  ext (i | i) (j | j) <;> by_cases h : i = j <;>
    simp [Gm, Am, Cm, Jm, Matrix.one_apply, Matrix.natCast_apply, Matrix.diagonal_apply, h]

/- English proof (translation)
Establish `h : Jm ℝ n = (Matrix.of fun (_ : Fin 1) (_ : Fin n) => (1 : ℝ))ᴴ * Matrix.of fun (_ : Fin 1) (_ : Fin n) => (1 : ℝ)`. Use extensionality with `i j`. Simplify using `[Jm, Matrix.mul_apply]`. Unfold `Cm`. Rewrite using `[h]`.

Conclude with `Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)`.
-/
theorem Cpos (n : ℕ) : (Cm ℝ n).PosDef := by
  have h : Jm ℝ n = (Matrix.of fun (_ : Fin 1) (_ : Fin n) => (1 : ℝ))ᴴ * Matrix.of fun (_ : Fin 1) (_ : Fin n) => (1 : ℝ) := by
    ext i j; simp [Jm, Matrix.mul_apply]
  unfold Cm
  rw [h]
  exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self _)

/- English proof (translation)
Establish `hn : ((n : ℝ) + 1) ≠ 0` using `by positivity`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[Matrix.mul_smul, CA, smul_smul, inv_mul_cancel₀ hn, one_smul]`.
-/
theorem Cinv (n : ℕ) : (Cm ℝ n)⁻¹ = ((n : ℝ) + 1)⁻¹ • Am ℝ n := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  apply Matrix.inv_eq_right_inv
  rw [Matrix.mul_smul, CA, smul_smul, inv_mul_cancel₀ hn, one_smul]

/- English proof (translation)
The claim follows from `(Cpos n).1`.
-/
theorem Csymm (n : ℕ) : (Cm ℝ n)ᴴ = Cm ℝ n := (Cpos n).1

/- English proof (translation)
Establish `hC : IsUnit (Cm ℝ n).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (Cpos n).isUnit`. Establish `hXH : ((Cm ℝ n)⁻¹)ᴴ = (Cm ℝ n)⁻¹`. Rewrite using `[Matrix.conjTranspose_nonsing_inv, Csymm]`. Establish `h1 : (Cm ℝ n)⁻¹ * Cm ℝ n = 1` using `Matrix.nonsing_inv_mul _ hC`. Establish `h2 : Cm ℝ n * (Cm ℝ n)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hC`.

Rewrite using `[Matrix.fromBlocks_conjTranspose, hXH, Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, h1, h2, Matrix.mul_assoc]`. Rewrite using `[Gm]`. Use `congr 1`. Rewrite using `[Cinv, smul_smul, ← add_smul, ← one_add_mul, add_comm (1 : ℝ), mul_inv_cancel₀ (by positivity), one_smul]`.
-/
theorem Gfac (n : ℕ) : Gm ℝ n =
    (Matrix.fromBlocks 1 0 (Cm ℝ n)⁻¹ 1)ᴴ * Matrix.fromBlocks (Cm ℝ n)⁻¹ 0 0 ((n : ℝ) • Cm ℝ n) *
      Matrix.fromBlocks 1 0 (Cm ℝ n)⁻¹ 1 := by
  have hC : IsUnit (Cm ℝ n).det := (Matrix.isUnit_iff_isUnit_det _).mp (Cpos n).isUnit
  have hXH : ((Cm ℝ n)⁻¹)ᴴ = (Cm ℝ n)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, Csymm]
  have h1 : (Cm ℝ n)⁻¹ * Cm ℝ n = 1 := Matrix.nonsing_inv_mul _ hC
  have h2 : Cm ℝ n * (Cm ℝ n)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hC
  rw [Matrix.fromBlocks_conjTranspose, hXH, Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [one_mul, mul_one, zero_mul, mul_zero, add_zero, zero_add,
    Matrix.mul_smul, Matrix.smul_mul, h1, h2, Matrix.mul_assoc]
  rw [Gm]
  congr 1
  rw [Cinv, smul_smul, ← add_smul, ← one_add_mul, add_comm (1 : ℝ), mul_inv_cancel₀ (by positivity),
    one_smul]

/- English proof (translation)
Apply `Int.cast_injective (α := ℝ)` to reduce the goal to its premises. Rewrite using `[Int.cast_det, Gmap, Gfac]`. Establish `hC : (Cm ℝ n).det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).mp (Cpos n).isUnit).ne_zero`. Simplify using `only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_smul, Matrix.det_nonsing_inv, Fintype.card_fin, star_one, one_mul, mul_one, Ring.inverse_eq_inv']`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts.
-/
theorem Gdet (n : ℕ) : (Gm ℤ n).det = (n : ℤ) ^ n := by
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_det, Gmap, Gfac]
  have hC : (Cm ℝ n).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp (Cpos n).isUnit).ne_zero
  simp only [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one,
    Matrix.det_smul, Matrix.det_nonsing_inv, Fintype.card_fin, star_one, one_mul, mul_one,
    Ring.inverse_eq_inv']
  push_cast
  field_simp

/- English proof (translation)
Establish `hn' : (n : ℝ) ≠ 0` using `Nat.cast_ne_zero.mpr hn.ne'`. Establish `hC : IsUnit (Cm ℝ n).det` using `(Matrix.isUnit_iff_isUnit_det _).mp (Cpos n).isUnit`. Establish `hD : ((n : ℝ) • Cm ℝ n).PosDef` using `(Cpos n).smul (by positivity)`. Use `haveI : Invertible ((n : ℝ) • Cm ℝ n) := hD.isUnit.invertible`. Establish `hG : Gm ℝ n = Matrix.fromBlocks (Am ℝ n) ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))ᴴ ((n : ℝ) • Cm ℝ n)`.

Rewrite using `[Gm, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]`. Establish `hinv : ((n : ℝ) • Cm ℝ n)⁻¹ = (n : ℝ)⁻¹ • (Cm ℝ n)⁻¹`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hn', one_smul, Matrix.mul_nonsing_inv _ hC]`. Establish `hA : Am ℝ n = ((n : ℝ) + 1) • (Cm ℝ n)⁻¹`.

Rewrite using `[Cinv, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]`. Establish `hS : Am ℝ n - (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) * ((n : ℝ) • Cm ℝ n)⁻¹ * ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))ᴴ = (Cm ℝ n)⁻¹`. Rewrite using `[hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial, hA]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul]`. Rewrite using `[inv_mul_cancel₀ hn', mul_one]`.

Use `module`. Establish `hPSD : (Gm ℝ n).PosSemidef`. Rewrite using `[hG, Matrix.PosDef.fromBlocks₂₂ _ _ hD, hS]`. Conclude with `(Cpos n).inv.posSemidef`. Establish `hU : IsUnit (Gm ℝ n)`.

Rewrite using `[Matrix.isUnit_iff_isUnit_det, ← Gmap, ← Int.cast_det, Gdet]`. Conclude with `isUnit_iff_ne_zero.mpr (by push_cast; exact pow_ne_zero _ hn')`. Conclude with `hPSD.posDef_iff_isUnit.mpr hU`.
-/
theorem Gpos (n : ℕ) (hn : 0 < n) : (Gm ℝ n).PosDef := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hC : IsUnit (Cm ℝ n).det := (Matrix.isUnit_iff_isUnit_det _).mp (Cpos n).isUnit
  have hD : ((n : ℝ) • Cm ℝ n).PosDef := (Cpos n).smul (by positivity)
  haveI : Invertible ((n : ℝ) • Cm ℝ n) := hD.isUnit.invertible
  have hG : Gm ℝ n = Matrix.fromBlocks (Am ℝ n) ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))
      ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))ᴴ ((n : ℝ) • Cm ℝ n) := by
    rw [Gm, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
  have hinv : ((n : ℝ) • Cm ℝ n)⁻¹ = (n : ℝ)⁻¹ • (Cm ℝ n)⁻¹ := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hn', one_smul,
      Matrix.mul_nonsing_inv _ hC]
  have hA : Am ℝ n = ((n : ℝ) + 1) • (Cm ℝ n)⁻¹ := by
    rw [Cinv, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  have hS : Am ℝ n - (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) * ((n : ℝ) • Cm ℝ n)⁻¹ *
      ((n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ))ᴴ = (Cm ℝ n)⁻¹ := by
    rw [hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial, hA]
    simp only [Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, smul_smul]
    rw [inv_mul_cancel₀ hn', mul_one]
    module
  have hPSD : (Gm ℝ n).PosSemidef := by
    rw [hG, Matrix.PosDef.fromBlocks₂₂ _ _ hD, hS]
    exact (Cpos n).inv.posSemidef
  have hU : IsUnit (Gm ℝ n) := by
    rw [Matrix.isUnit_iff_isUnit_det, ← Gmap, ← Int.cast_det, Gdet]
    exact isUnit_iff_ne_zero.mpr (by push_cast; exact pow_ne_zero _ hn')
  exact hPSD.posDef_iff_isUnit.mpr hU

/- English proof (translation)
Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih => rw [pow_succ, ih, Matrix.fromBlocks_multiply]`. Simplify using `[pow_succ]`.
-/
theorem blockPow {n : ℕ} (T S : Matrix (Fin n) (Fin n) ℤ) (i : ℕ) :
    (Matrix.fromBlocks T 0 0 S) ^ i = Matrix.fromBlocks (T ^ i) 0 0 (S ^ i) := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, ih, Matrix.fromBlocks_multiply]; simp [pow_succ]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [Finset.sum_range_succ, ih, blockPow]`. Simplify using `only [Finset.sum_range_succ, Matrix.fromBlocks_add, add_zero]`.
-/
theorem blockSum {n : ℕ} (T S : Matrix (Fin n) (Fin n) ℤ) (m : ℕ) :
    ∑ i ∈ Finset.range m, (Matrix.fromBlocks T 0 0 S) ^ i =
      Matrix.fromBlocks (∑ i ∈ Finset.range m, T ^ i) 0 0 (∑ i ∈ Finset.range m, S ^ i) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih, blockPow]; simp only [Finset.sum_range_succ, Matrix.fromBlocks_add, add_zero]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Use extensionality with `a b`. Establish `h0 : Fin.ofNat (n + 1) 0 = 0` using `Fin.ext (by simp)`. Simplify using `[Matrix.one_apply, h0]`.

Consider the case `succ k ih`. Rewrite using `[pow_succ, ih]`. Use extensionality with `a b`. Establish `hs : Fin.ofNat (n + 1) (k + 1) = 1 + Fin.ofNat (n + 1) k`. Apply `Fin.ext` to reduce the goal to its premises.

Simplify using `[Fin.val_add, Nat.add_mod, add_comm]`. Rewrite using `[Matrix.of_apply, hs, Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, add_assoc]`.
-/
private theorem exists_ne_zero_smul_mem_of_mem_span' (n k : ℕ) :
    (Matrix.of fun a b : Fin (n + 1) => if a = b + 1 then (1 : ℤ) else 0) ^ k =
      Matrix.of fun a b : Fin (n + 1) => if a = b + Fin.ofNat (n + 1) k then (1 : ℤ) else 0 := by
  induction k with
  | zero =>
    ext a b
    have h0 : Fin.ofNat (n + 1) 0 = 0 := Fin.ext (by simp)
    simp [Matrix.one_apply, h0]
  | succ k ih =>
    rw [pow_succ, ih]
    ext a b
    have hs : Fin.ofNat (n + 1) (k + 1) = 1 + Fin.ofNat (n + 1) k := by
      apply Fin.ext
      simp [Fin.val_add, Nat.add_mod, add_comm]
    rw [Matrix.of_apply, hs, Matrix.mul_apply]
    simp only [Matrix.of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true, add_assoc]

/- English proof (translation)
Repeatedly rewrite using `[exists_ne_zero_smul_mem_of_mem_span']`. Use extensionality with `a b`. Rewrite using `[Matrix.sum_apply]`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun k => if a = b + Fin.ofNat (n + 1) k then (1 : ℤ) else 0) (n + 1)]`.

Establish `hv : ∀ i : Fin (n + 1), Fin.ofNat (n + 1) (i : ℕ) = i` using `fun i => Fin.ext (by simp [Nat.mod_eq_of_lt i.isLt])`. Simplify using `only [hv]`. Establish `hiff : ∀ i : Fin (n + 1), (a = b + i) ↔ (i = a - b)` using `fun i => by`. Apply the tactic sequence `constructor <;> intro h <;> subst h <;> simp`. Simplify using `only [hiff, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.
-/
private theorem main_lemma_2 (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (Matrix.of fun a b : Fin (n + 1) => if a = b + 1 then (1 : ℤ) else 0) ^ k =
      Matrix.of fun _ _ : Fin (n + 1) => (1 : ℤ) := by
  simp_rw [exists_ne_zero_smul_mem_of_mem_span']
  ext a b
  rw [Matrix.sum_apply]
  simp only [Matrix.of_apply]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => if a = b + Fin.ofNat (n + 1) k then (1 : ℤ) else 0) (n + 1)]
  have hv : ∀ i : Fin (n + 1), Fin.ofNat (n + 1) (i : ℕ) = i := fun i =>
    Fin.ext (by simp [Nat.mod_eq_of_lt i.isLt])
  simp only [hv]
  have hiff : ∀ i : Fin (n + 1), (a = b + i) ↔ (i = a - b) := fun i => by
    constructor <;> intro h <;> subst h <;> simp
  simp only [hiff, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/- English proof (translation)
Take `⟨P, hP⟩ : ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ, P = Matrix.of fun a b => if a = b + 1 then 1 else 0` from `⟨_, rfl⟩`. Take `⟨B, hB⟩ : ∃ B : Matrix (Fin (n + 1)) (Fin n) ℤ, B = Matrix.of fun a c => (if a = c.succ then 1 else 0) - (if a = 0 then 1 else 0)` from `⟨_, rfl⟩`. Take `⟨L, hL⟩ : ∃ L : Matrix (Fin n) (Fin (n + 1)) ℤ, L = Matrix.of fun r a => if a = r.succ then 1 else 0` from `⟨_, rfl⟩`. Take `⟨X, hX⟩ : ∃ X : Matrix (Fin (n + 1)) (Fin 1) ℤ, X = Matrix.of fun a _ => if a = 0 then 1 else 0` from `⟨_, rfl⟩`. Take `⟨Y, hY⟩ : ∃ Y : Matrix (Fin 1) (Fin (n + 1)) ℤ, Y = Matrix.of fun _ _ => 1` from `⟨_, rfl⟩`.

Take `⟨Z, hZ⟩ : ∃ Z : Matrix (Fin (n + 1)) (Fin 1) ℤ, Z = Matrix.of fun _ _ => 1` from `⟨_, rfl⟩`. Establish `hLB : L * B = 1`. Use extensionality with `r c`. Simplify using `[hL, hB, Matrix.mul_apply, Matrix.one_apply, Fin.succ_ne_zero]`. Establish `hBL : B * L = 1 - X * Y`.

Use extensionality with `a b`. Apply the tactic sequence `refine Fin.cases ?_ (fun b' => ?_) b <;>`. Simplify using `[hL, hB, hX, hY, Matrix.mul_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib, Fin.succ_ne_zero, eq_comm]`. Establish `hYP : Y * P = Y`. Use extensionality with `j b`.

Simplify using `[hY, hP, Matrix.mul_apply]`. Establish `hYB : Y * B = 0`. Use extensionality with `j c`. Simplify using `[hY, hB, Matrix.mul_apply, Finset.sum_sub_distrib]`. Establish `hPP : Pᵀ * P = 1`.

Use extensionality with `a b`. Simplify using `[hP, Matrix.mul_apply, Matrix.one_apply]`. Conclude with `if_congr eq_comm rfl rfl`. Establish `hC : Cm ℤ n = Bᵀ * B`. Use extensionality with `r c`.

Simplify using `[Cm, Jm, hB, Matrix.mul_apply, Matrix.one_apply, mul_sub, sub_mul, Finset.sum_sub_distrib, Fin.succ_ne_zero]`. Conclude with `if_congr eq_comm rfl rfl`. Establish `hsumP : ∑ k ∈ Finset.range (n + 1), P ^ k = Z * Y`. Rewrite using `[hP, main_lemma_2]`. Use extensionality with `a b`.

Simplify using `[hZ, hY, Matrix.mul_apply]`. Establish `hBU : B * (L * P * B) = P * B`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hBL, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc X Y P, hYP, Matrix.mul_assoc X Y B, hYB, Matrix.mul_zero, sub_zero]`. Establish `hpow : ∀ k : ℕ, B * (L * P * B) ^ k = P ^ k * B`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Rewrite using `[pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hBU, ← Matrix.mul_assoc, ← pow_succ]`. Use `⟨L * P * B, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hC]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.transpose_mul B]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = (P * B)ᵀ * (P * B) := by rw [hBU]`.

Use `_ = Bᵀ * (Pᵀ * P) * B := by`. Rewrite using `[Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Bᵀ * B := by rw [hPP, Matrix.mul_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.mul_assoc, Matrix.mul_sum]`. Use `_ = L * ∑ k ∈ Finset.range (n + 1), P ^ k * B := by simp only [hpow]`. Use `_ = L * ((∑ k ∈ Finset.range (n + 1), P ^ k) * B) := by rw [Matrix.sum_mul]`. Use `_ = 0 := by rw [hsumP, Matrix.mul_assoc Z Y B, hYB, Matrix.mul_zero, Matrix.mul_zero]`.
-/
private theorem main_lemma_3 (n : ℕ) : ∃ U : Matrix (Fin n) (Fin n) ℤ,
    Uᵀ * Cm ℤ n * U = Cm ℤ n ∧ ∑ k ∈ Finset.range (n + 1), U ^ k = 0 := by
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ,
      P = Matrix.of fun a b => if a = b + 1 then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin (n + 1)) (Fin n) ℤ,
      B = Matrix.of fun a c => (if a = c.succ then 1 else 0) - (if a = 0 then 1 else 0) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin n) (Fin (n + 1)) ℤ,
      L = Matrix.of fun r a => if a = r.succ then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin (n + 1)) (Fin 1) ℤ,
      X = Matrix.of fun a _ => if a = 0 then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin 1) (Fin (n + 1)) ℤ, Y = Matrix.of fun _ _ => 1 := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin (n + 1)) (Fin 1) ℤ, Z = Matrix.of fun _ _ => 1 := ⟨_, rfl⟩
  have hLB : L * B = 1 := by
    ext r c
    simp [hL, hB, Matrix.mul_apply, Matrix.one_apply, Fin.succ_ne_zero]
  have hBL : B * L = 1 - X * Y := by
    ext a b
    refine Fin.cases ?_ (fun b' => ?_) b <;>
      simp [hL, hB, hX, hY, Matrix.mul_apply, Matrix.one_apply, sub_mul, Finset.sum_sub_distrib,
        Fin.succ_ne_zero, eq_comm]
  have hYP : Y * P = Y := by
    ext j b
    simp [hY, hP, Matrix.mul_apply]
  have hYB : Y * B = 0 := by
    ext j c
    simp [hY, hB, Matrix.mul_apply, Finset.sum_sub_distrib]
  have hPP : Pᵀ * P = 1 := by
    ext a b
    simp [hP, Matrix.mul_apply, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  have hC : Cm ℤ n = Bᵀ * B := by
    ext r c
    simp [Cm, Jm, hB, Matrix.mul_apply, Matrix.one_apply, mul_sub, sub_mul, Finset.sum_sub_distrib,
      Fin.succ_ne_zero]
    exact if_congr eq_comm rfl rfl
  have hsumP : ∑ k ∈ Finset.range (n + 1), P ^ k = Z * Y := by
    rw [hP, main_lemma_2]
    ext a b
    simp [hZ, hY, Matrix.mul_apply]
  have hBU : B * (L * P * B) = P * B := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hBL, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc X Y P, hYP, Matrix.mul_assoc X Y B, hYB, Matrix.mul_zero, sub_zero]
  have hpow : ∀ k : ℕ, B * (L * P * B) ^ k = P ^ k * B := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hBU, ← Matrix.mul_assoc, ← pow_succ]
  refine ⟨L * P * B, ?_, ?_⟩
  · rw [hC]
    calc (L * P * B)ᵀ * (Bᵀ * B) * (L * P * B)
        = (B * (L * P * B))ᵀ * (B * (L * P * B)) := by
          rw [Matrix.transpose_mul B]
          simp only [Matrix.mul_assoc]
      _ = (P * B)ᵀ * (P * B) := by rw [hBU]
      _ = Bᵀ * (Pᵀ * P) * B := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = Bᵀ * B := by rw [hPP, Matrix.mul_one]
  · calc ∑ k ∈ Finset.range (n + 1), (L * P * B) ^ k
        = L * B * ∑ k ∈ Finset.range (n + 1), (L * P * B) ^ k := by rw [hLB, Matrix.one_mul]
      _ = L * ∑ k ∈ Finset.range (n + 1), B * (L * P * B) ^ k := by
          rw [Matrix.mul_assoc, Matrix.mul_sum]
      _ = L * ∑ k ∈ Finset.range (n + 1), P ^ k * B := by simp only [hpow]
      _ = L * ((∑ k ∈ Finset.range (n + 1), P ^ k) * B) := by rw [Matrix.sum_mul]
      _ = 0 := by rw [hsumP, Matrix.mul_assoc Z Y B, hYB, Matrix.mul_zero, Matrix.mul_zero]

/- English proof (translation)
Take `⟨m, hm⟩` from `he`. Take `⟨U, hUC, hUsum⟩` from `main_lemma_3 n`. Establish `hU1 : U ^ (n + 1) = 1`. Establish `h` using `geom_sum_mul U (n + 1)`. Rewrite `h` using `[hUsum, zero_mul]`.

Conclude with `(sub_eq_zero.mp h.symm)`. Take `⟨V, hV⟩ : ∃ V : Matrix (Fin n) (Fin n) ℤ, V = U ^ n` from `⟨_, rfl⟩`. Establish `hUV : U * V = 1` using `by rw [hV, ← pow_succ', hU1]`. Establish `hVU : V * U = 1` using `by rw [hV, ← pow_succ, hU1]`. Establish `hcomm : Commute V U` using `by show V * U = U * V`.

Rewrite using `[hVU, hUV]`. Establish `hVsum : ∑ k ∈ Finset.range (n + 1), V ^ k = 0`. Establish `h1 : ∀ i ∈ Finset.range (n + 1), V ^ n * U ^ i = V ^ (n - i)`. Introduce `i hi`. Establish `hi' : i ≤ n` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)`.

Rewrite using `[show V ^ n = V ^ (n - i) * V ^ i by rw [← pow_add, Nat.sub_add_cancel hi'], mul_assoc, ← hcomm.mul_pow, hVU, one_pow, mul_one]`. Rewrite using `[← Finset.sum_range_reflect]`. Simplify using `only [Nat.add_sub_cancel]`. Rewrite using `[← Finset.sum_congr rfl h1, ← Finset.mul_sum, hUsum, mul_zero]`. Establish `hW : V * Am ℤ n * Vᵀ = Am ℤ n`.

Establish `hWC : V * Am ℤ n * Vᵀ * Cm ℤ n = ((n : ℤ) + 1) • 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.transpose_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = V * (Am ℤ n * Cm ℤ n) * U := by`.

Rewrite using `[hUV, Matrix.transpose_one]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`. Use `_ = ((n : ℤ) + 1) • 1 := by`. Rewrite using `[AC, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hVU]`. Establish `h2 : ((n : ℤ) + 1) • (V * Am ℤ n * Vᵀ) = ((n : ℤ) + 1) • Am ℤ n`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[CA, Matrix.mul_smul, Matrix.mul_one]`. Use `_ = (V * Am ℤ n * Vᵀ * Cm ℤ n) * Am ℤ n := by simp only [Matrix.mul_assoc]`. Use `_ = ((n : ℤ) + 1) • Am ℤ n := by rw [hWC, Matrix.smul_mul, Matrix.one_mul]`. Conclude with `smul_right_injective _ (by positivity : ((n : ℤ) + 1) ≠ 0) h2`.

Establish `hUtVt : Uᵀ * Vᵀ = 1` using `by rw [← Matrix.transpose_mul, hVU, Matrix.transpose_one]`. Use `⟨Gm ℤ n, Matrix.fromBlocks Vᵀ 0 0 U, n ^ m, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [Fintype.card_sum, Fintype.card_fin]`. Use linear arithmetic over natural numbers and integers. Use `⟨by rw [Gmap]; exact Gpos n hn, ?_⟩` and prove the remaining obligations.

Introduce `i`. Break down `i with i | i` into its components or cases. Simplify using `[Gm, Am, Jm, Matrix.natCast_apply] first`. Consider the case `exact ⟨m, hm⟩`. Consider the case `exact ⟨(m : ℤ), by rw [hm]; push_cast; ring⟩`.

Simplify using `[Gm, Cm, Jm, Matrix.natCast_apply]`. Rewrite using `[Matrix.fromBlocks_transpose, Matrix.transpose_transpose, Matrix.transpose_zero, Gm, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_zero, hW, hVU, hUtVt, hUC]`. Establish `hT : ∑ i ∈ Finset.range (n + 1), Vᵀ ^ i = 0`. Repeatedly rewrite using `[← Matrix.transpose_pow]`.

Rewrite using `[← Matrix.transpose_sum, hVsum, Matrix.transpose_zero]`. Rewrite using `[blockSum, hT, hUsum, Matrix.fromBlocks_zero]`. Rewrite using `[Gdet]`. Substitute `hm` using the available equality. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hq : (n + 1 - 1) / 2 = m` using `by omega`. Rewrite using `[hq]`. Establish `h1 : (-(n : ℤ)) ≡ 1 [ZMOD ((n + 1 : ℕ) : ℤ)]` using `Int.modEq_iff_dvd.mpr ⟨1, by push_cast; ring⟩`. Establish `h2` using `h1.pow m`.

Rewrite `h2` using `[neg_pow, one_pow]`. Move the coercions through the operations in `at h2 ⊢`. Conclude with `h2`.
-/
theorem main (n : ℕ) (hn : 0 < n) (he : Even n) :
    ∃ (G S : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℤ) (t : ℕ), LatD (n + 1) G S t := by
  obtain ⟨m, hm⟩ := he
  obtain ⟨U, hUC, hUsum⟩ := main_lemma_3 n
  have hU1 : U ^ (n + 1) = 1 := by
    have h := geom_sum_mul U (n + 1)
    rw [hUsum, zero_mul] at h
    exact (sub_eq_zero.mp h.symm)
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin n) (Fin n) ℤ, V = U ^ n := ⟨_, rfl⟩
  have hUV : U * V = 1 := by rw [hV, ← pow_succ', hU1]
  have hVU : V * U = 1 := by rw [hV, ← pow_succ, hU1]
  have hcomm : Commute V U := by
    show V * U = U * V
    rw [hVU, hUV]
  have hVsum : ∑ k ∈ Finset.range (n + 1), V ^ k = 0 := by
    have h1 : ∀ i ∈ Finset.range (n + 1), V ^ n * U ^ i = V ^ (n - i) := by
      intro i hi
      have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [show V ^ n = V ^ (n - i) * V ^ i by rw [← pow_add, Nat.sub_add_cancel hi'], mul_assoc,
        ← hcomm.mul_pow, hVU, one_pow, mul_one]
    rw [← Finset.sum_range_reflect]
    simp only [Nat.add_sub_cancel]
    rw [← Finset.sum_congr rfl h1, ← Finset.mul_sum, hUsum, mul_zero]
  have hW : V * Am ℤ n * Vᵀ = Am ℤ n := by
    have hWC : V * Am ℤ n * Vᵀ * Cm ℤ n = ((n : ℤ) + 1) • 1 := by
      calc V * Am ℤ n * Vᵀ * Cm ℤ n = V * Am ℤ n * Vᵀ * (Uᵀ * Cm ℤ n * U) := by rw [hUC]
        _ = V * Am ℤ n * (U * V)ᵀ * Cm ℤ n * U := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
        _ = V * (Am ℤ n * Cm ℤ n) * U := by
          rw [hUV, Matrix.transpose_one]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
        _ = ((n : ℤ) + 1) • 1 := by
          rw [AC, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hVU]
    have h2 : ((n : ℤ) + 1) • (V * Am ℤ n * Vᵀ) = ((n : ℤ) + 1) • Am ℤ n := by
      calc ((n : ℤ) + 1) • (V * Am ℤ n * Vᵀ) = V * Am ℤ n * Vᵀ * (Cm ℤ n * Am ℤ n) := by
            rw [CA, Matrix.mul_smul, Matrix.mul_one]
        _ = (V * Am ℤ n * Vᵀ * Cm ℤ n) * Am ℤ n := by simp only [Matrix.mul_assoc]
        _ = ((n : ℤ) + 1) • Am ℤ n := by rw [hWC, Matrix.smul_mul, Matrix.one_mul]
    exact smul_right_injective _ (by positivity : ((n : ℤ) + 1) ≠ 0) h2
  have hUtVt : Uᵀ * Vᵀ = 1 := by rw [← Matrix.transpose_mul, hVU, Matrix.transpose_one]
  refine ⟨Gm ℤ n, Matrix.fromBlocks Vᵀ 0 0 U, n ^ m, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  · refine ⟨by rw [Gmap]; exact Gpos n hn, ?_⟩
    intro i
    rcases i with i | i
    · simp [Gm, Am, Jm, Matrix.natCast_apply]
      first
        | exact ⟨m, hm⟩
        | exact ⟨(m : ℤ), by rw [hm]; push_cast; ring⟩
    · simp [Gm, Cm, Jm, Matrix.natCast_apply]

  · rw [Matrix.fromBlocks_transpose, Matrix.transpose_transpose, Matrix.transpose_zero, Gm, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, smul_zero, hW, hVU, hUtVt, hUC]
  · have hT : ∑ i ∈ Finset.range (n + 1), Vᵀ ^ i = 0 := by
      simp_rw [← Matrix.transpose_pow]
      rw [← Matrix.transpose_sum, hVsum, Matrix.transpose_zero]
    rw [blockSum, hT, hUsum, Matrix.fromBlocks_zero]
  · rw [Gdet]
    subst hm
    push_cast
    ring
  · have hq : (n + 1 - 1) / 2 = m := by omega
    rw [hq]
    have h1 : (-(n : ℤ)) ≡ 1 [ZMOD ((n + 1 : ℕ) : ℤ)] :=
      Int.modEq_iff_dvd.mpr ⟨1, by push_cast; ring⟩
    have h2 := h1.pow m
    rw [neg_pow, one_pow] at h2
    push_cast at h2 ⊢
    exact h2

/- English proof (translation)
Introduce `p hp hp2`. Establish `hpos : 0 < p - 1`. Use `hp.two_le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨G, S, t, h⟩` from `main (p - 1) hpos (hp.even_sub_one hp2)`.

Rewrite `h` using `[Nat.sub_add_cancel hp.one_le]`. Conclude with `⟨G, S, t, h⟩`.
-/
theorem exists_latD : ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ (G S : Matrix (Fin (p - 1) ⊕ Fin (p - 1)) (Fin (p - 1) ⊕ Fin (p - 1)) ℤ) (t : ℕ), LatD p G S t := by
  intro p hp hp2
  have hpos : 0 < p - 1 := by
    have := hp.two_le
    omega
  obtain ⟨G, S, t, h⟩ := main (p - 1) hpos (hp.even_sub_one hp2)
  rw [Nat.sub_add_cancel hp.one_le] at h
  exact ⟨G, S, t, h⟩

end GlobalTheory.HilbertThetaSeries.EvenLat

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.HilbertThetaSeries.EvenLat.exists_latD | exact GlobalTheory.HilbertThetaSeries.EvenLat.exists_latD | (intros; apply GlobalTheory.HilbertThetaSeries.EvenLat.exists_latD <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.exists_evenPositiveDefinite_intMatrix_det_sq : ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ (G S : Matrix (Fin (p - 1) ⊕ Fin (p - 1)) (Fin (p - 1) ⊕ Fin (p - 1)) ℤ) (t : ℕ), LatD p G S t := by
  first | exact @GlobalTheory.HilbertThetaSeries.EvenLat.exists_latD | exact GlobalTheory.HilbertThetaSeries.EvenLat.exists_latD | (intros; apply GlobalTheory.HilbertThetaSeries.EvenLat.exists_latD <;> assumption)
