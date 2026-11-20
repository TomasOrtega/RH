import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TrivialParameterBound
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

noncomputable section

namespace GlobalTheory.GraphShear

open Matrix

/- English proof (translation)
Unfold `Formalism.UG.GLint Formalism.UG.bc`. Establish `hinj : Function.Injective (O.subtype.mapMatrix : Matrix ι ι O →+* Matrix ι ι L)` using `fun A B h => by`. Use extensionality with `i j`. Conclude with `congrFun (congrFun h i) j`. Establish `hA : O.subtype.mapMatrix (Matrix.of fun i j => (⟨x.1 i j, h1 i j⟩ : O)) = x.1`.

Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hB : O.subtype.mapMatrix (Matrix.of fun i j => (⟨(x⁻¹).1 i j, h2 i j⟩ : O)) = (x⁻¹).1`. Use extensionality with `i j`. Both sides reduce to the same expression.

Use `⟨⟨Matrix.of fun i j => (⟨x.1 i j, h1 i j⟩ : O), Matrix.of fun i j => (⟨(x⁻¹).1 i j, h2 i j⟩ : O), ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_mul, map_one, hA, hB]`. Conclude with `Units.mul_inv x`. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[map_mul, map_one, hA, hB]`. Conclude with `Units.inv_mul x`. Conclude with `Units.ext hA`.
-/
theorem mem_GLint_of_entries {L : Type} [Field L] {ι : Type} [Fintype ι] [DecidableEq ι] {O : Subring L}
    {x : GL ι L} (h1 : ∀ i j, x.1 i j ∈ O) (h2 : ∀ i j, (x⁻¹).1 i j ∈ O) : x ∈ Formalism.UG.GLint ι O := by
  unfold Formalism.UG.GLint Formalism.UG.bc
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix ι ι O →+* Matrix ι ι L) := fun A B h => by
    ext i j
    exact congrFun (congrFun h i) j
  have hA : O.subtype.mapMatrix (Matrix.of fun i j => (⟨x.1 i j, h1 i j⟩ : O)) = x.1 := by
    ext i j
    rfl
  have hB : O.subtype.mapMatrix (Matrix.of fun i j => (⟨(x⁻¹).1 i j, h2 i j⟩ : O)) = (x⁻¹).1 := by
    ext i j
    rfl
  refine ⟨⟨Matrix.of fun i j => (⟨x.1 i j, h1 i j⟩ : O), Matrix.of fun i j => (⟨(x⁻¹).1 i j, h2 i j⟩ : O), ?_, ?_⟩, ?_⟩
  · apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.mul_inv x
  · apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.inv_mul x
  · exact Units.ext hA

/- English proof (translation)
Establish `hsc : ∀ a : ℤ, (ϖ ^ (-a).toNat - 1) * (ϖ ^ a.toNat - 1) = 0 ∧ ϖ ^ a.toNat - 1 + 1 = ϖ ^ max a 0 ∧ ϖ ^ a * (1 + (ϖ ^ (-a).toNat - 1)) = ϖ ^ max a 0 ∧ ϖ ^ a - (ϖ ^ a.toNat - 1) = ϖ ^ min a 0`. Introduce `a`. Break down `le_total 0 a with h | h` into its components or cases. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le h`. Establish `e1 : (-(m : ℤ)).toNat = 0` using `by omega`.

Establish `e2 : (m : ℤ).toNat = m` using `by omega`. Establish `e3 : max (m : ℤ) 0 = m` using `by omega`. Establish `e4 : min (m : ℤ) 0 = 0` using `by omega`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e1, e2, e3, e4, pow_zero, sub_self, zero_mul, zpow_natCast, zpow_zero, sub_add_cancel, add_zero, mul_one] <;> ring`. Take `⟨m, rfl⟩` from `Int.exists_eq_neg_ofNat h`.

Establish `e1 : (-(-(m : ℤ))).toNat = m` using `by omega`. Establish `e2 : (-(m : ℤ)).toNat = 0` using `by omega`. Establish `e3 : max (-(m : ℤ)) 0 = 0` using `by omega`. Establish `e4 : min (-(m : ℤ)) 0 = -(m : ℤ)` using `by omega`. Establish `hm : ϖ ^ m ≠ 0` using `pow_ne_zero m h0`.

Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [e1, e2, e3, e4, hm, h0]`. Establish `hmem : ∀ (M : Matrix (Fin n) (Fin n) L) (f : Fin n → L), (∀ i, f i ∈ O) → M = Matrix.diagonal f → ∀ i j, M i j ∈ O`. Introduce `M f hf hM i j`. Rewrite using `[hM, Matrix.diagonal_apply]`. Use `split_ifs`.

Conclude with `hf i`. Conclude with `O.zero_mem`. Establish `hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) L) i j ∈ O` using `hmem 1 (fun _ => 1) (fun _ => O.one_mem) Matrix.diagonal_one.symm`. Take `⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) L, B = Matrix.diagonal fun i => ϖ ^ (-d i).toNat - 1` from `⟨_, rfl⟩`. Take `⟨C, hC⟩ : ∃ C : Matrix (Fin n) (Fin n) L, C = Matrix.diagonal fun i => ϖ ^ (d i).toNat - 1` from `⟨_, rfl⟩`.

Establish `hBO : ∀ i j, B i j ∈ O` using `hmem B _ (fun _ => O.sub_mem (O.pow_mem hϖO _) O.one_mem) hB`. Establish `hCO : ∀ i j, C i j ∈ O` using `hmem C _ (fun _ => O.sub_mem (O.pow_mem hϖO _) O.one_mem) hC`. Establish `hBC : B * C = 0`. Rewrite using `[hB, hC, Matrix.diagonal_mul_diagonal]`. Simplify using `only [(hsc _).1, Matrix.diagonal_zero]`.

Establish `hCB : C * B = 0`. Rewrite using `[hB, hC, Matrix.diagonal_mul_diagonal]`. Simplify using `only [mul_comm (ϖ ^ (d _).toNat - 1), (hsc _).1, Matrix.diagonal_zero]`. Establish `hC1 : C + 1 = Matrix.diagonal (fun i => ϖ ^ max (d i) 0)`. Rewrite using `[hC, ← Matrix.diagonal_one, Matrix.diagonal_add]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(hsc (d i)).2.1`. Establish `hTB : t.1 * (1 + B) = Matrix.diagonal (fun i => ϖ ^ max (d i) 0)`. Rewrite using `[ht, hB, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(hsc (d i)).2.2.1`. Establish `hTC : t.1 - C = Matrix.diagonal (fun i => ϖ ^ min (d i) 0)`. Rewrite using `[ht, hC, Matrix.diagonal_sub]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `(hsc (d i)).2.2.2`. Generalize the expression as in `(finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) = e`. Establish `hfb : ∀ (P Q R S : Matrix (Fin n) (Fin n) L), (∀ i j, P i j ∈ O) → (∀ i j, Q i j ∈ O) → (∀ i j, R i j ∈ O) → (∀ i j, S i j ∈ O) → ∀ a b, Matrix.fromBlocks P Q R S a b ∈ O`.

Introduce `P Q R S hP hQ hR hS a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Conclude with `hP a b`. Conclude with `hQ a b`. Conclude with `hR a b`.

Conclude with `hS a b`. Establish `hUU : Matrix.fromBlocks 1 B C 1 * Matrix.fromBlocks 1 (-B) (-C) 1 = 1`. Rewrite using `[Matrix.fromBlocks_multiply]`. Simplify using `[hBC, hCB, Matrix.fromBlocks_one]`. Establish `hUU' : Matrix.fromBlocks 1 (-B) (-C) 1 * Matrix.fromBlocks 1 B C 1 = 1`.

Rewrite using `[Matrix.fromBlocks_multiply]`. Simplify using `[hBC, hCB, Matrix.fromBlocks_one]`. Set `U : GL (Fin (n + n)) L` to `⟨(Matrix.fromBlocks 1 B C 1).submatrix e.symm e.symm, (Matrix.fromBlocks 1 (-B) (-C) 1).submatrix e.symm e.symm, by rw [Matrix.submatrix_mul_equiv, hUU, Matrix.submatrix_one_equiv], by rw [Matrix.submatrix_mul_equiv, hUU', Matrix.submatrix_one_equiv]⟩`. Establish `hU : U ∈ Formalism.UG.GLint (Fin (n + n)) O`. Apply `mem_GLint_of_entries` to reduce the goal to its premises.

Introduce `i j`. Conclude with `hfb 1 B C 1 hone hBO hCO hone (e.symm i) (e.symm j)`. Introduce `i j`. Conclude with `hfb 1 (-B) (-C) 1 hone (fun a b => O.neg_mem (hBO a b)) (fun a b => O.neg_mem (hCO a b)) hone (e.symm i) (e.symm j)`. Establish `hblk : ∀ x y : GL (Fin n) L, x ∈ Formalism.UG.GLint (Fin n) O → y ∈ Formalism.UG.GLint (Fin n) O → blkGL e (x, y) ∈ Formalism.UG.GLint (Fin (n + n)) O`.

Introduce `x y hx hy`. Unfold `Formalism.UG.GLint at hx hy ⊢`. Take `⟨x', rfl⟩` from `hx`. Take `⟨y', rfl⟩` from `hy`. Conclude with `⟨blkGL e (x', y'), bc_blkGL e O.subtype x' y'⟩`.

Use `⟨blkGL e (k₂⁻¹, k₁) * U, Subgroup.mul_mem _ (hblk _ _ (Subgroup.inv_mem _ hk₂) hk₁) hU, ?_⟩` and prove the remaining obligations. Establish `hprod : blkGL e (k₁ * t * k₂, 1) * (blkGL e (k₂⁻¹, k₁) * U) = blkGL e (k₁ * t, k₁) * U`. Rewrite using `[← mul_assoc, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel_right, one_mul]`. Rewrite using `[hprod]`. Establish `hsub : ((blkGL e (k₁ * t, k₁) * U : GL (Fin (n + n)) L) : Matrix (Fin (n + n)) (Fin (n + n)) L).submatrix e e = Matrix.fromBlocks (k₁.1 * t.1) (k₁.1 * t.1 * B) (k₁.1 * C) k₁.1`.

Rewrite using `[Units.val_mul, val_blkGL]`. Use `show ((Matrix.fromBlocks _ 0 0 _).submatrix e.symm e.symm * (Matrix.fromBlocks 1 B C 1).submatrix e.symm e.symm).submatrix e e = _`. Rewrite using `[Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id, Matrix.fromBlocks_multiply]`. Simplify using `[Units.val_mul]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Unfold `KeepsDiag leviMat`. Rewrite using `[hsub]`. Simplify using `only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂]`. Establish `h1 : C + 1 = t.1 * (1 + B)` using `by rw [hC1, hTB]`. Combine the equalities or inequalities in the displayed calculation.

Unfold `leviMat`. Rewrite using `[hsub]`. Simplify using `only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂]`. Rewrite using `[← hTB, mul_add, mul_one, mul_add, mul_assoc]`. Unfold `quotMat`.

Rewrite using `[hsub]`. Simplify using `only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁]`. Rewrite using `[← hTC, mul_sub]`.
-/
theorem exists_kappa {L : Type} [Field L] {O : Subring L} {n : ℕ} {ϖ : L} (h0 : ϖ ≠ 0) (hϖO : ϖ ∈ O)
    (d : Fin n → ℤ) (t k₁ k₂ : GL (Fin n) L) (ht : t.1 = Matrix.diagonal (fun i => ϖ ^ d i))
    (hk₁ : k₁ ∈ Formalism.UG.GLint (Fin n) O) (hk₂ : k₂ ∈ Formalism.UG.GLint (Fin n) O) :
    ∃ κ ∈ Formalism.UG.GLint (Fin (n + n)) O,
      KeepsDiag finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 ∧
      leviMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 =
        k₁.1 * Matrix.diagonal (fun i => ϖ ^ max (d i) 0) ∧
      quotMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 =
        k₁.1 * Matrix.diagonal (fun i => ϖ ^ min (d i) 0) := by
  have hsc : ∀ a : ℤ, (ϖ ^ (-a).toNat - 1) * (ϖ ^ a.toNat - 1) = 0 ∧
      ϖ ^ a.toNat - 1 + 1 = ϖ ^ max a 0 ∧
      ϖ ^ a * (1 + (ϖ ^ (-a).toNat - 1)) = ϖ ^ max a 0 ∧
      ϖ ^ a - (ϖ ^ a.toNat - 1) = ϖ ^ min a 0 := by
    intro a
    rcases le_total 0 a with h | h
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
      have e1 : (-(m : ℤ)).toNat = 0 := by omega
      have e2 : (m : ℤ).toNat = m := by omega
      have e3 : max (m : ℤ) 0 = m := by omega
      have e4 : min (m : ℤ) 0 = 0 := by omega
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e1, e2, e3, e4, pow_zero, sub_self, zero_mul, zpow_natCast, zpow_zero,
        sub_add_cancel, add_zero, mul_one] <;> ring
    · obtain ⟨m, rfl⟩ := Int.exists_eq_neg_ofNat h
      have e1 : (-(-(m : ℤ))).toNat = m := by omega
      have e2 : (-(m : ℤ)).toNat = 0 := by omega
      have e3 : max (-(m : ℤ)) 0 = 0 := by omega
      have e4 : min (-(m : ℤ)) 0 = -(m : ℤ) := by omega
      have hm : ϖ ^ m ≠ 0 := pow_ne_zero m h0
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [e1, e2, e3, e4, hm, h0]
  have hmem : ∀ (M : Matrix (Fin n) (Fin n) L) (f : Fin n → L), (∀ i, f i ∈ O) → M = Matrix.diagonal f →
      ∀ i j, M i j ∈ O := by
    intro M f hf hM i j
    rw [hM, Matrix.diagonal_apply]
    split_ifs
    · exact hf i
    · exact O.zero_mem
  have hone : ∀ i j, (1 : Matrix (Fin n) (Fin n) L) i j ∈ O :=
    hmem 1 (fun _ => 1) (fun _ => O.one_mem) Matrix.diagonal_one.symm
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin n) L, B = Matrix.diagonal fun i => ϖ ^ (-d i).toNat - 1 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Matrix (Fin n) (Fin n) L, C = Matrix.diagonal fun i => ϖ ^ (d i).toNat - 1 := ⟨_, rfl⟩
  have hBO : ∀ i j, B i j ∈ O := hmem B _ (fun _ => O.sub_mem (O.pow_mem hϖO _) O.one_mem) hB
  have hCO : ∀ i j, C i j ∈ O := hmem C _ (fun _ => O.sub_mem (O.pow_mem hϖO _) O.one_mem) hC
  have hBC : B * C = 0 := by
    rw [hB, hC, Matrix.diagonal_mul_diagonal]
    simp only [(hsc _).1, Matrix.diagonal_zero]
  have hCB : C * B = 0 := by
    rw [hB, hC, Matrix.diagonal_mul_diagonal]
    simp only [mul_comm (ϖ ^ (d _).toNat - 1), (hsc _).1, Matrix.diagonal_zero]
  have hC1 : C + 1 = Matrix.diagonal (fun i => ϖ ^ max (d i) 0) := by
    rw [hC, ← Matrix.diagonal_one, Matrix.diagonal_add]
    congr 1
    funext i
    exact (hsc (d i)).2.1
  have hTB : t.1 * (1 + B) = Matrix.diagonal (fun i => ϖ ^ max (d i) 0) := by
    rw [ht, hB, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact (hsc (d i)).2.2.1
  have hTC : t.1 - C = Matrix.diagonal (fun i => ϖ ^ min (d i) 0) := by
    rw [ht, hC, Matrix.diagonal_sub]
    congr 1
    funext i
    exact (hsc (d i)).2.2.2
  generalize (finSumFinEquiv : Fin n ⊕ Fin n ≃ Fin (n + n)) = e
  have hfb : ∀ (P Q R S : Matrix (Fin n) (Fin n) L), (∀ i j, P i j ∈ O) → (∀ i j, Q i j ∈ O) →
      (∀ i j, R i j ∈ O) → (∀ i j, S i j ∈ O) → ∀ a b, Matrix.fromBlocks P Q R S a b ∈ O := by
    intro P Q R S hP hQ hR hS a b
    rcases a with a | a <;> rcases b with b | b
    · exact hP a b
    · exact hQ a b
    · exact hR a b
    · exact hS a b
  have hUU : Matrix.fromBlocks 1 B C 1 * Matrix.fromBlocks 1 (-B) (-C) 1 = 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp [hBC, hCB, Matrix.fromBlocks_one]
  have hUU' : Matrix.fromBlocks 1 (-B) (-C) 1 * Matrix.fromBlocks 1 B C 1 = 1 := by
    rw [Matrix.fromBlocks_multiply]
    simp [hBC, hCB, Matrix.fromBlocks_one]
  let U : GL (Fin (n + n)) L :=
    ⟨(Matrix.fromBlocks 1 B C 1).submatrix e.symm e.symm, (Matrix.fromBlocks 1 (-B) (-C) 1).submatrix e.symm e.symm,
      by rw [Matrix.submatrix_mul_equiv, hUU, Matrix.submatrix_one_equiv],
      by rw [Matrix.submatrix_mul_equiv, hUU', Matrix.submatrix_one_equiv]⟩
  have hU : U ∈ Formalism.UG.GLint (Fin (n + n)) O := by
    apply mem_GLint_of_entries
    · intro i j
      exact hfb 1 B C 1 hone hBO hCO hone (e.symm i) (e.symm j)
    · intro i j
      exact hfb 1 (-B) (-C) 1 hone (fun a b => O.neg_mem (hBO a b)) (fun a b => O.neg_mem (hCO a b)) hone
        (e.symm i) (e.symm j)
  have hblk : ∀ x y : GL (Fin n) L, x ∈ Formalism.UG.GLint (Fin n) O → y ∈ Formalism.UG.GLint (Fin n) O →
      blkGL e (x, y) ∈ Formalism.UG.GLint (Fin (n + n)) O := by
    intro x y hx hy
    unfold Formalism.UG.GLint at hx hy ⊢
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨blkGL e (x', y'), bc_blkGL e O.subtype x' y'⟩
  refine ⟨blkGL e (k₂⁻¹, k₁) * U, Subgroup.mul_mem _ (hblk _ _ (Subgroup.inv_mem _ hk₂) hk₁) hU, ?_⟩
  have hprod : blkGL e (k₁ * t * k₂, 1) * (blkGL e (k₂⁻¹, k₁) * U) = blkGL e (k₁ * t, k₁) * U := by
    rw [← mul_assoc, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel_right, one_mul]
  rw [hprod]
  have hsub : ((blkGL e (k₁ * t, k₁) * U : GL (Fin (n + n)) L) : Matrix (Fin (n + n)) (Fin (n + n)) L).submatrix e e =
      Matrix.fromBlocks (k₁.1 * t.1) (k₁.1 * t.1 * B) (k₁.1 * C) k₁.1 := by
    rw [Units.val_mul, val_blkGL]
    show ((Matrix.fromBlocks _ 0 0 _).submatrix e.symm e.symm *
      (Matrix.fromBlocks 1 B C 1).submatrix e.symm e.symm).submatrix e e = _
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id,
      Matrix.fromBlocks_multiply]
    simp [Units.val_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold KeepsDiag leviMat
    rw [hsub]
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂, Matrix.toBlocks_fromBlocks₂₁,
      Matrix.toBlocks_fromBlocks₂₂]
    have h1 : C + 1 = t.1 * (1 + B) := by rw [hC1, hTB]
    calc k₁.1 * C + k₁.1 = k₁.1 * (C + 1) := by rw [mul_add, mul_one]
      _ = k₁.1 * (t.1 * (1 + B)) := by rw [h1]
      _ = k₁.1 * t.1 + k₁.1 * t.1 * B := by rw [mul_add, mul_one, mul_add, mul_assoc]
  · unfold leviMat
    rw [hsub]
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₁₂]
    rw [← hTB, mul_add, mul_one, mul_add, mul_assoc]
  · unfold quotMat
    rw [hsub]
    simp only [Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁]
    rw [← hTC, mul_sub]

/- English proof (translation)
Establish `hdet : Valued.v k.1.det = 1`. Establish `hk'` using `hk`. Unfold `Formalism.UG.GLint at hk'`. Take `⟨y, hy⟩` from `hk'`. Establish `hkmat : k.1 = O.subtype.mapMatrix y.1`.

Rewrite using `[← hy]`. Both sides reduce to the same expression. Establish `hinv : (k⁻¹).1 = O.subtype.mapMatrix (y⁻¹).1`. Rewrite using `[← hy, ← map_inv]`. Both sides reduce to the same expression.

Establish `hm1 : k.1.det ∈ O`. Rewrite using `[hkmat, ← RingHom.map_det]`. Conclude with `(y.1.det).2`. Establish `hm2 : (k⁻¹).1.det ∈ O`. Rewrite using `[hinv, ← RingHom.map_det]`.

Conclude with `((y⁻¹).1.det).2`. Establish `hmul : k.1.det * (k⁻¹).1.det = 1`. Rewrite using `[← Matrix.det_mul, Units.mul_inv, Matrix.det_one]`. Establish `hv : Valued.v k.1.det * Valued.v (k⁻¹).1.det = 1`. Rewrite using `[← map_mul, hmul, map_one]`.

Use `le_antisymm (hO _ hm1) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hpow : ∀ i, Valued.v (ϖ ^ f i) = ((Multiplicative.ofAdd (-(f i)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`. Introduce `i`. Rewrite using `[map_zpow₀, hϖ, ← WithZero.coe_zpow]`.

Use `congr 1`. Rewrite using `[← ofAdd_zsmul]`. Use `congr 1`. Simplify using the standard rewrite rules. Establish `hD : Valued.v (Matrix.diagonal fun i => ϖ ^ f i).det = ((Multiplicative.ofAdd (-(∑ i, f i)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`.

Rewrite using `[Matrix.det_diagonal, map_prod, Finset.prod_congr rfl (fun i _ => hpow i), ← Finset.sum_neg_distrib, ofAdd_sum]`. Conclude with `(map_prod (WithZero.coeMonoidHom : Multiplicative ℤ →* WithZero (Multiplicative ℤ)) _ _).symm`. Establish `hord : ∀ (z : L) (s : ℤ), Valued.v z = ((Multiplicative.ofAdd (-s) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → ordL z = s`. Introduce `z s hz`. Unfold `Formalism.UG.ordL`.

Use `split_ifs with h`. Rewrite `h` using `[hz]`. Conclude with `absurd h WithZero.coe_ne_zero`. Establish `h2 : WithZero.unzero h = Multiplicative.ofAdd (-s)` using `WithZero.coe_injective (by rw [WithZero.coe_unzero, hz])`. Rewrite using `[h2, toAdd_ofAdd, neg_neg]`.

Rewrite using `[Matrix.det_mul]`. Conclude with `hord _ _ (by rw [map_mul, hdet, one_mul, hD])`.
-/
theorem ordL_det_mul_diagonal {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {O : Subring L}
    (hO : ∀ x ∈ O, Valued.v x ≤ (1 : WithZero (Multiplicative ℤ))) {n : ℕ} {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {k : GL (Fin n) L} (hk : k ∈ Formalism.UG.GLint (Fin n) O) (f : Fin n → ℤ) :
    ordL (k.1 * Matrix.diagonal fun i => ϖ ^ f i).det = ∑ i, f i := by
  have hdet : Valued.v k.1.det = 1 := by
    have hk' := hk
    unfold Formalism.UG.GLint at hk'
    obtain ⟨y, hy⟩ := hk'
    have hkmat : k.1 = O.subtype.mapMatrix y.1 := by
      rw [← hy]
      rfl
    have hinv : (k⁻¹).1 = O.subtype.mapMatrix (y⁻¹).1 := by
      rw [← hy, ← map_inv]
      rfl
    have hm1 : k.1.det ∈ O := by
      rw [hkmat, ← RingHom.map_det]
      exact (y.1.det).2
    have hm2 : (k⁻¹).1.det ∈ O := by
      rw [hinv, ← RingHom.map_det]
      exact ((y⁻¹).1.det).2
    have hmul : k.1.det * (k⁻¹).1.det = 1 := by
      rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
    have hv : Valued.v k.1.det * Valued.v (k⁻¹).1.det = 1 := by
      rw [← map_mul, hmul, map_one]
    refine le_antisymm (hO _ hm1) ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v k.1.det * Valued.v (k⁻¹).1.det := hv.symm
      _ ≤ Valued.v k.1.det * 1 := mul_le_mul' le_rfl (hO _ hm2)
      _ = Valued.v k.1.det := mul_one _
  have hpow : ∀ i, Valued.v (ϖ ^ f i) =
      ((Multiplicative.ofAdd (-(f i)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    intro i
    rw [map_zpow₀, hϖ, ← WithZero.coe_zpow]
    congr 1
    rw [← ofAdd_zsmul]
    congr 1
    simp
  have hD : Valued.v (Matrix.diagonal fun i => ϖ ^ f i).det =
      ((Multiplicative.ofAdd (-(∑ i, f i)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    rw [Matrix.det_diagonal, map_prod, Finset.prod_congr rfl (fun i _ => hpow i), ← Finset.sum_neg_distrib, ofAdd_sum]
    exact (map_prod (WithZero.coeMonoidHom : Multiplicative ℤ →* WithZero (Multiplicative ℤ)) _ _).symm
  have hord : ∀ (z : L) (s : ℤ),
      Valued.v z = ((Multiplicative.ofAdd (-s) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) → ordL z = s := by
    intro z s hz
    unfold Formalism.UG.ordL
    split_ifs with h
    · rw [hz] at h
      exact absurd h WithZero.coe_ne_zero
    · have h2 : WithZero.unzero h = Multiplicative.ofAdd (-s) :=
        WithZero.coe_injective (by rw [WithZero.coe_unzero, hz])
      rw [h2, toAdd_ofAdd, neg_neg]
  rw [Matrix.det_mul]
  exact hord _ _ (by rw [map_mul, hdet, one_mul, hD])

/- English proof (translation)
Introduce `E _ _ w n ϖ hϖ d t k₁ k₂ ht hk₁ hk₂`. Establish `hK : ∀ m, GlobalTheory.LFun.KGL w m = Formalism.UG.GLint (Fin m) (w.adicCompletionIntegers E).toSubring` using `fun m => rfl`. Establish `hϖ' : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))` using `hϖ`. Establish `hO : ∀ x ∈ (w.adicCompletionIntegers E).toSubring, Valued.v x ≤ (1 : WithZero (Multiplicative ℤ))` using `fun x hx => hx`. Establish `hϖO : ϖ ∈ (w.adicCompletionIntegers E).toSubring` using `by show Valued.v ϖ ≤ 1`.

Rewrite using `[hϖ']`. Conclude with `le_of_lt (by decide)`. Establish `h0 : ϖ ≠ 0`. Introduce `h`. Rewrite `hϖ'` using `[h, map_zero]`.

Conclude with `WithZero.zero_ne_coe hϖ'`. Rewrite `hk₁`, `hk₂` using `[hK]`. Take `⟨κ, hκ, h1, h2, h3⟩` from `exists_kappa h0 hϖO d t k₁ k₂ ht hk₁ hk₂`. Use `⟨κ, (hK _).symm ▸ hκ, h1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h2]`.

Conclude with `ordL_det_mul_diagonal hO hϖ' hk₁ _`. Rewrite using `[h3]`. Conclude with `ordL_det_mul_diagonal hO hϖ' hk₁ _`.
-/
theorem graph_shear : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (d : Fin n → ℤ) (t k₁ k₂ : GL (Fin n) (w.adicCompletion E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → k₁ ∈ KGL w n → k₂ ∈ KGL w n → ∃ κ ∈ KGL w (n + n), KeepsDiag finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1 ∧ ordL (leviMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, max (d i) 0 ∧ ordL (quotMat finSumFinEquiv (blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ).1).det = ∑ i, min (d i) 0 := by
  intro E _ _ w n ϖ hϖ d t k₁ k₂ ht hk₁ hk₂
  have hK : ∀ m, GlobalTheory.LFun.KGL w m = Formalism.UG.GLint (Fin m) (w.adicCompletionIntegers E).toSubring := fun m => rfl
  have hϖ' : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := hϖ
  have hO : ∀ x ∈ (w.adicCompletionIntegers E).toSubring, Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) :=
    fun x hx => hx
  have hϖO : ϖ ∈ (w.adicCompletionIntegers E).toSubring := by
    show Valued.v ϖ ≤ 1
    rw [hϖ']
    exact le_of_lt (by decide)
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ'
    exact WithZero.zero_ne_coe hϖ'
  rw [hK] at hk₁ hk₂
  obtain ⟨κ, hκ, h1, h2, h3⟩ := exists_kappa h0 hϖO d t k₁ k₂ ht hk₁ hk₂
  refine ⟨κ, (hK _).symm ▸ hκ, h1, ?_, ?_⟩
  · rw [h2]
    exact ordL_det_mul_diagonal hO hϖ' hk₁ _
  · rw [h3]
    exact ordL_det_mul_diagonal hO hϖ' hk₁ _

end GlobalTheory.GraphShear

end
