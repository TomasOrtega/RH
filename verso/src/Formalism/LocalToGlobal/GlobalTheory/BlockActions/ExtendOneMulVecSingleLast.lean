import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.Br

open Matrix

variable {R : Type} [CommRing R] {n : ℕ}

def blk1 (g : Matrix (Fin n) (Fin n) R) : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  (fromBlocks g 0 0 (1 : Matrix (Fin 1) (Fin 1) R)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def inclusionAlt : Matrix (Fin (n + 1)) (Fin n) R := of fun a b => if a = Fin.castSucc b then 1 else 0

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [mul_apply, inclusionAlt, of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last`. Establish `hne : ∀ x : Fin n, ¬ (Fin.last n = Fin.castSucc x)` using `fun x hx => (Fin.castSucc_lt_last x).ne' hx`.

Simplify using `[blk1, hne, finSumFinEquiv_symm_last]`. Consider the case `cast i`. Simplify using `[blk1, Fin.castSucc_inj]`.
-/
theorem extendOne_mul_inclusion (g : Matrix (Fin n) (Fin n) R) : blk1 g * inclusionAlt = inclusionAlt * g := by
  ext i j
  simp only [mul_apply, inclusionAlt, of_apply, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  induction i using Fin.lastCases with
  | last =>
    have hne : ∀ x : Fin n, ¬ (Fin.last n = Fin.castSucc x) := fun x hx => (Fin.castSucc_lt_last x).ne' hx
    simp [blk1, hne, finSumFinEquiv_symm_last]
  | cast i =>
    simp [blk1, Fin.castSucc_inj]

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[Matrix.mulVec_single_one]`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => simp [blk1]`. Consider the case `cast i => simp [blk1, Fin.castSucc_ne_last]`.
-/
theorem extendOne_mulVec_single_last (g : Matrix (Fin n) (Fin n) R) : blk1 g *ᵥ Pi.single (Fin.last n) 1 = Pi.single (Fin.last n) 1 := by
  ext i
  rw [Matrix.mulVec_single_one]
  induction i using Fin.lastCases with
  | last => simp [blk1]
  | cast i => simp [blk1, Fin.castSucc_ne_last]

/- English proof (translation)
Simplify using `[blk1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]`.
-/
theorem det_extendOne (g : Matrix (Fin n) (Fin n) R) : (blk1 g).det = g.det := by
  simp [blk1, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

def extM {E : Type} [Field E] (φ : E →+* R) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (g : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  B.map φ * blk1 g * (B.map φ)⁻¹

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [inclusionAlt, map_apply, of_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem eN_map {E : Type} [Field E] (φ : E →+* R) : (inclusionAlt : Matrix (Fin (n + 1)) (Fin n) E).map φ = inclusionAlt := by
  ext a b
  simp only [inclusionAlt, map_apply, of_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `hBu : IsUnit (B.map φ).det`. Establish `e1 : (B.map φ).det = φ B.det` using `(RingHom.map_det φ B).symm`. Rewrite using `[e1]`. Conclude with `hB.map φ`. Establish `hinv : (B.map φ)⁻¹ * B.map φ = 1` using `Matrix.nonsing_inv_mul _ hBu`.

Establish `hA : A.map φ = B.map φ * inclusionAlt`. Rewrite using `[← hBA, Matrix.map_mul, eN_map]`. Establish `hz : (fun a => φ (z a)) = B.map φ *ᵥ Pi.single (Fin.last n) 1`. Rewrite using `[← hBz]`. Use extensionality with `a`.

Simplify using `only [Matrix.mulVec, dotProduct, map_apply, map_sum, map_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `congr 1`. Distinguish the cases in `hk : k = Fin.last n`. Substitute `hk` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Pi.single_apply, hk]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hA, extM, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (B.map φ)⁻¹, hinv, Matrix.one_mul, extendOne_mul_inclusion, ← Matrix.mul_assoc]`. Rewrite using `[hz, extM, Matrix.mulVec_mulVec, Matrix.mul_assoc _ _ (B.map φ), hinv, Matrix.mul_one, ← Matrix.mulVec_mulVec, extendOne_mulVec_single_last]`.

Introduce `hg`. Rewrite using `[extM, Matrix.det_mul, Matrix.det_mul]`. Use `(hBu.mul ?_).mul ?_` and prove the remaining obligations. Rewrite using `[det_extendOne]`. Conclude with `hg`.

Conclude with `Matrix.isUnit_nonsing_inv_det _ hBu`.
-/
theorem extM_spec {E : Type} [Field E] (φ : E →+* R) (A : Matrix (Fin (n + 1)) (Fin n) E) (z : Fin (n + 1) → E)
    (B : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hBA : B * inclusionAlt = A) (hBz : B *ᵥ Pi.single (Fin.last n) 1 = z) (hB : IsUnit B.det)
    (g : Matrix (Fin n) (Fin n) R) :
    extM φ B g * A.map φ = A.map φ * g ∧ extM φ B g *ᵥ (fun a => φ (z a)) = (fun a => φ (z a)) ∧
      (IsUnit g.det → IsUnit (extM φ B g).det) := by
  have hBu : IsUnit (B.map φ).det := by
    have e1 : (B.map φ).det = φ B.det := (RingHom.map_det φ B).symm
    rw [e1]
    exact hB.map φ
  have hinv : (B.map φ)⁻¹ * B.map φ = 1 := Matrix.nonsing_inv_mul _ hBu
  have hA : A.map φ = B.map φ * inclusionAlt := by
    rw [← hBA, Matrix.map_mul, eN_map]
  have hz : (fun a => φ (z a)) = B.map φ *ᵥ Pi.single (Fin.last n) 1 := by
    rw [← hBz]
    ext a
    simp only [Matrix.mulVec, dotProduct, map_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    by_cases hk : k = Fin.last n
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, extM, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (B.map φ)⁻¹, hinv,
      Matrix.one_mul, extendOne_mul_inclusion, ← Matrix.mul_assoc]
  · rw [hz, extM, Matrix.mulVec_mulVec, Matrix.mul_assoc _ _ (B.map φ), hinv, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, extendOne_mulVec_single_last]
  · intro hg
    rw [extM, Matrix.det_mul, Matrix.det_mul]
    refine (hBu.mul ?_).mul ?_
    · rw [det_extendOne]; exact hg
    · exact Matrix.isUnit_nonsing_inv_det _ hBu

/- English proof (translation)
Substitute `hN` using the available equality. Use `set B : Matrix (Fin (n + 1)) (Fin (n + 1)) E := Matrix.of (fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) with hBdef`. Establish `hBA : B * inclusionAlt = A`. Use extensionality with `a b`. Simplify using `only [mul_apply, inclusionAlt, of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, hBdef, Fin.coe_castSucc, b.isLt, dif_pos]`.

Establish `hBz : B *ᵥ Pi.single (Fin.last n) 1 = z`. Use extensionality with `a`. Rewrite using `[Matrix.mulVec_single_one]`. Simplify using `[hBdef]`. Conclude with `⟨extM φ B g, extM_spec φ A z B hBA hBz hB g⟩`.
-/
theorem ext_general {E : Type} [Field E] (φ : E →+* R) {N : ℕ} (hN : n + 1 = N) (A : Matrix (Fin N) (Fin n) E) (z : Fin N → E)
    (hB : IsUnit (Matrix.of (fun a (b : Fin N) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a)).det)
    (g : Matrix (Fin n) (Fin n) R) :
    ∃ G : Matrix (Fin N) (Fin N) R, G * A.map φ = A.map φ * g ∧ G *ᵥ (fun a => φ (z a)) = (fun a => φ (z a)) ∧
      (IsUnit g.det → IsUnit G.det) := by
  subst hN
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) E :=
    Matrix.of (fun a (b : Fin (n + 1)) => if hb : (b : ℕ) < n then A a ⟨b, hb⟩ else z a) with hBdef
  have hBA : B * inclusionAlt = A := by
    ext a b
    simp only [mul_apply, inclusionAlt, of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, hBdef, Fin.coe_castSucc, b.isLt, dif_pos]
  have hBz : B *ᵥ Pi.single (Fin.last n) 1 = z := by
    ext a
    rw [Matrix.mulVec_single_one]
    simp [hBdef]
  exact ⟨extM φ B g, extM_spec φ A z B hBA hBz hB g⟩

end Formalism.L2.GlobalTheoryTheory.Br
