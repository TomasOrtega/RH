import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible

open GlobalTheory.UnitLemma Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.UnitLemma.BaseChange

variable {K : UQ} (B : InvAlg K)

/- English proof (translation)
Unfold `InvAlg.herm`. Rewrite using `[Finset.mul_sum, Finset.sum_mul, map_sum]`.
-/
theorem herm_sum_left {ι : Type} (s : Finset ι) (x : B.A) (f : ι → B.A) (z : B.A) :
    B.herm x (∑ k ∈ s, f k) z = ∑ k ∈ s, B.herm x (f k) z := by
  unfold InvAlg.herm
  rw [Finset.mul_sum, Finset.sum_mul, map_sum]

/- English proof (translation)
Unfold `InvAlg.herm`. Rewrite using `[map_sum, Finset.mul_sum, map_sum]`.
-/
theorem herm_sum_right {ι : Type} (s : Finset ι) (x y : B.A) (f : ι → B.A) :
    B.herm x y (∑ k ∈ s, f k) = ∑ k ∈ s, B.herm x y (f k) := by
  unfold InvAlg.herm
  rw [map_sum, Finset.mul_sum, map_sum]

/- English proof (translation)
Establish `hi` using `e.sum_toMatrix_smul_self e' i`. Establish `hj` using `e.sum_toMatrix_smul_self e' j`. Rewrite using `[← hi, ← hj, herm_sum_left]`. Repeatedly rewrite using `[herm_sum_right, GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, he]`. Simplify using `[mul_ite, Finset.sum_ite_eq]`.
-/
theorem herm_basis_change (x : B.A) {n : ℕ} (e e' : Module.Basis (Fin n) K.E B.A)
    (he : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (i j : Fin n) :
    B.herm x (e' i) (e' j) = ∑ k, e.toMatrix e' k i * K.c (e.toMatrix e' k j) := by
  have hi := e.sum_toMatrix_smul_self e' i
  have hj := e.sum_toMatrix_smul_self e' j
  rw [← hi, ← hj, herm_sum_left]
  simp_rw [herm_sum_right, GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, he]
  simp [mul_ite, Finset.sum_ite_eq]

/- English proof (translation)
Introduce `K B x n e e' he`. Establish `key` using `herm_basis_change B x e e' he`. Establish `hm : ∀ i j, (((e.toMatrix e').map K.c)ᵀ * e.toMatrix e') j i = B.herm x (e' i) (e' j)`. Introduce `i j`. Rewrite using `[key, Matrix.mul_apply]`.

Conclude with `Finset.sum_congr rfl fun k _ => by simp [mul_comm]`. Prove the components needed by the constructor for the conclusion. Introduce `h'`. Use extensionality with `j i`. Rewrite using `[hm, h', Matrix.one_apply]`.

Distinguish the cases in `hij : i = j`. Simplify using `[hij]`. Simplify using `[hij, Ne.symm hij]`. Introduce `hu i j`. Rewrite using `[← hm, hu, Matrix.one_apply]`.

Distinguish the cases in `hij : i = j`. Simplify using `[hij]`. Simplify using `[hij, Ne.symm hij]`.
-/
theorem orthonormal_iff_unitary : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (n : ℕ) (e e' : Module.Basis (Fin n) K.E B.A),
    (∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) →
    ((∀ i j, B.herm x (e' i) (e' j) = if i = j then 1 else 0) ↔ ((e.toMatrix e').map K.c)ᵀ * e.toMatrix e' = 1) := by
  intro K B x n e e' he
  have key := herm_basis_change B x e e' he
  have hm : ∀ i j, (((e.toMatrix e').map K.c)ᵀ * e.toMatrix e') j i = B.herm x (e' i) (e' j) := by
    intro i j
    rw [key, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by simp [mul_comm]
  constructor
  · intro h'
    ext j i
    rw [hm, h', Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · intro hu i j
    rw [← hm, hu, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]

end GlobalTheory.UnitLemma.BaseChange
